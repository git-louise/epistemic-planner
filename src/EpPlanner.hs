{- | Plan extraction for iterated epistemic actions.
 
Given a knowledge structure, a finite repertoire of epistemic actions schemas, 
and a goal formula, this tool searches for action sequences after which the goal 
formula holds. If it cannot find such a sequence the tool tries to certify this. 
If a plan is found, the tool re-executes it along an independent single-pointed path. 
It then uses SMCDEL to check if the goal formula holds. The result of this replay is 
printed next to the found plan.

The tool implements four different search variants (modes), so that 
their runtimes, the maximal event law size and vocabulary size, as well as
the certificates that may have been found can be compared on identical inputs.

* "tree" corresponds to the naïve approach. The search tree is branched over the 
action sequences: one structure and guards per structure are generated for each 
action sequence. At depth @d@, this results in @m^d@ structures. A plan can be 
found or reported not found for the given horizon, but this mode cannot be used 
to prove that no plan exists.


* "union" is the composed approach. It constructs one structure per horizon. 
It does not prune atoms. Since the vocabulary increases with every round, this 
variant cannot be used to detect a literal fixpoint.

* "prune" uses the composed public-choice construction that is used in the union
mode and pruning. This mode executes the full Psi scan of Proposition 5.6 after 
every round. It can detect literal fixpoints and prove that no further application 
of any action can affect the evaluation of the goal formula.

* "full" uses the composed public-choice construction and prunes relativized to 
the agents that are mentioned in the goal formula and the event laws. This mode 
also searches for a bisimulation link (Definition A.12) using the geometric schedule 
of Remark A.15, after performing the agreement precheck described there.

= Usage

@
stack run epistemic-planner -- [EXAMPLE ...] [VARIANT ...] [OPTION ...]
@
where the examples, variants and options themselves can be given in any order and 
will then run in the given order. At least one variant must be given to the tool, 
either as a bare word (@tree@, @union@, @prune@, @full@)  or using the option 
 @--variants=@. 

The named examples are peekA, peekB, share, relay, askA, askB, tell and
askAll. The scaled families of examples are muddyN, askN and askbN, so 
muddy4 or ask3 are also valid names. For example:

@
stack run epistemic-planner -- peekA prune full --quiet
stack run epistemic-planner -- tell muddy2 tree union prune full --max=8 --csv=out.csv
@

Options:

[@--max=K@] sets the horizon up to which the tool searches for a plan to @K@. 
The default is @K@=10.

[@--timeout=S@] sets a time limit of @S@ seconds for each search (that is, 
for each pair of example and search variant). The default is 60.

[@--variants=v1,v2@] adds the search variants @v1@ and @v2@ to the search. 
Variants that are mentioned multiple times are ignored.

[@--csv=FILE@] saves the results of the run to FILE. 

[@--quiet@] hides the details of the search.

-}


{-# LANGUAGE DerivingStrategies #-}

module Main (main) where

import Control.Exception (evaluate)
import Data.Bits ((.&.))
import Data.Char (isDigit)
import Data.HasCacBDD (Bdd, allVarsOfSorted, anySatWith, bot, con, conSet, dis,
    disSet, equ, evaluateFun, exists_, existsSet, forallSet, imp, neg, relabel,
    restrict, sizeOf, top, var, xor)
import Data.List (foldl', intercalate, elemIndex, intersect, nub, sort, sortBy,
    stripPrefix, subsequences, (\\))
import Data.Maybe (fromMaybe)
import Data.Ord (comparing)
import System.CPUTime (getCPUTime)
import System.Environment (getArgs)
import System.Exit (die)
import System.Timeout (timeout)
import Text.Printf (printf)

import SMCDEL.Language (Agent, Form (Conj, Disj, Equi, K, Kw, Neg, PrpF),
    HasAgents (agentsOf), HasVocab (vocabOf), Prp (P), agentsInForm)
import SMCDEL.Symbolic.S5 (KnowStruct (KnS), State, bddOf, evalViaBdd, boolBddOf)


-- * Reading the SMCDEL types

-- | The atom @P n@ names the BDD kernel variable @n@. This removes the constructor
-- wherever a raw index is needed.
unP :: Prp -> Int
unP (P n) = n

-- | The state law of a knowledge structure. Its satisfying assignments over
-- the vocabulary are exactly the states.
lawOf :: KnowStruct -> Bdd
lawOf (KnS _ law _) = law  -- pattern match on the three fields, return the law l

-- | The atoms that agent @i@ observes. Two states are @i@-indistinguishable iff
-- they agree on this set. An unknown agent observes nothing.
obsFor :: KnowStruct -> Agent -> [Prp]
obsFor (KnS _ _ obs) i = fromMaybe [] (lookup i obs)
-- obs is an association list [(Agent, [Prp])]
-- lookup i obs returns Just [Prp] or Nothing, fromMaybe [] gives [] for Nothing.

{- | The characteristic conjunction of a single state over a vocabulary: one
literal per atom, positive iff the state contains it. Its unique satisfying
assignment over the vocabulary is the state itself.
-}
cubeOf :: [Prp] -> State -> Bdd
cubeOf voc s = conSet [ (if p `elem` s then id else neg) (var (unP p)) | p <- voc ]
-- id leaves the literal positive and neg negates it
-- conSet takes the conjunction of a list of BDDs

-- | The characteristic BDD xi_S of a belief state, it is true exactly at the
-- given states.
xiOf :: [Prp] -> [State] -> Bdd
xiOf voc = disSet . map (cubeOf voc)
--  map (cubeOf voc) turns each state into its cube BDD;
--  disSet takes the disjunction of all those cubes.

{- | The 'relable' from HasCacBDD requires that its mapping is sorted by source. 
Further, the rebuild there is only correct if the map is order-preserving. If
either condition fails, it returns a wrong BDD without raising any error.
In this file we therefore use this version of relabelling, where sources and 
targets both need to be strictly increasing. This also rules out duplicates. The
check is linear. 
-}
relabelSafe :: [(Int, Int)] -> Bdd -> Bdd
relabelSafe rel
    | increasing (map fst rel) && increasing (map snd rel) = relabel rel
    | otherwise = error $
        "relabelSafe: mapping must be sorted and order-preserving, got "
        ++ show rel
  where
    increasing :: [Int] -> Bool
    increasing xs = and (zipWith (<) xs (drop 1 xs))  -- strictly, pairwise

-- * Multi-pointed events

{- | A multi-pointed event consists of a symbolic knowledge transformer together
with a designated set of possible events.
The transformer has event atoms, it restricts the admissible events by
an event law, and it specifies which of the event atoms are observed by each 
of the agents. The designated set of possible events is represented by its 
characteristic BDD. It determines which of the events are considered as actual 
outcomes.
We keep the event law as a formula instead a BDD, because it may contain modal 
operators whose interpretation depends on the knowledge structure to which the 
event is applied. The multi-pointedness allows the planner to reason about plan 
existence without having to select a single outcome in advance.
-}
data MPEvent = MPEvent
    { mpProps :: ![Prp]             -- ^ the fresh event atoms
    , mpLaw   :: !Form              -- ^ the event law, possibly modal
    , mpObs   :: ![(Agent, [Prp])]  -- ^ the added observables, per agent
    , mpPts   :: !Bdd               -- ^ the designated set, as a BDD xi_X
    }

{- | The knowledge transformation described in Chapter 2, F times \X: the
vocabulary increases by the event atoms, the law is conjoined with the
translated event law, and every agent's observables increase by what the
event makes them observe. only the transformer part of the event 
is used here, the designated set goes in the guard. Because of this, the 
translated law is returned, as the guard recursion needs it as a separate
factor instead of just inside the new state law.
-}
applyEvent :: KnowStruct -> MPEvent -> (KnowStruct, Bdd)
applyEvent kns@(KnS v law obs) t = (KnS v' (con law lawB) obs', lawB)
  where
    -- Translate the (possibly modal) event law against the current structure.
    -- Modal operators like K_a phi are evaluated in F; fresh V+ atoms stay free.
    lawB :: Bdd
    lawB = bddOf kns (mpLaw t)
    -- Extend the vocabulary: append the new event atoms after the base atoms.
    -- (round r has the ids 1000r..1000r+999).
    v' :: [Prp]
    v' = v ++ mpProps t
    -- Extend the observables, keep O_i, add whatever O+_i the action gives.
    obs' :: [(Agent, [Prp])]
    obs' = [ (i, o ++ fromMaybe [] (lookup i (mpObs t))) | (i, o) <- obs ]


-- * Repertoires and the public-choice union

-- | A schema for a multi-pointed event. This is @(\X_i, X_i)@ from Chapter 3, 
-- but before the event atoms are instantiated for a given planning round.
-- Note that we do not store the concrete event atoms here, we use a schema to 
-- store an ordered list of event-atom names and functions that 
-- can then be instantiated for a given round with the round's vocabulary
data MPEventSchema = MPEventSchema
    { esName  :: !String                       -- ^ display name
    , esAtoms :: ![String]                     -- ^ event-atom names
    , esLaw   :: !([Prp] -> Form)              -- ^ the event law as a function
    , esObs   :: !([Prp] -> [(Agent, [Prp])])  -- ^ observables as a function
    , esPts   :: !([Prp] -> Bdd)               -- ^ the designated set
    }


-- | The repertoire of possible actions (wrapping a list of schemas)
newtype Repertoire = Repertoire
    { unRepertoire :: [MPEventSchema]
    }

-- | Returns the event schemas contained in a repertoire.
branchesOf :: Repertoire -> [MPEventSchema]
branchesOf = unRepertoire

-- | Metadata stored for atoms created by taking the union
data AtomInfo = AtomInfo
    { aiRound :: !Int    
    , aiBlock :: !Int     -- ^ 0 if choice bit, 1 if branch atom
    , aiIdx   :: !Int     -- ^ index
    , aiName  :: !String  -- ^ name ("c1@3" for example)
    } deriving stock (Show) 


-- | The smallest @k@ s.t. @2^k >= n@
-- To find out the amount of choice bits needed to index m branches
ceilLog2 :: Int -> Int
ceilLog2 n = head [ k | k <- [(0 :: Int) ..], 2 ^ k >= n ]  
-- ceilLog2 1 = 0, ceilLog2 3 = 2, ceilLog2 4 = 2, ceilLog2 5 = 3.

-- | Builds the public-choice union for planning round @r@. 
-- Combines the event schemas in the repertoire into one 'MPEvent'
instantiateUnion ::
    [Agent] ->  -- the agents of the planning problem
    Repertoire ->  --the Repertoire
    Int ->  -- the round number @r@
    (MPEvent, [Prp], [[Prp]], [(Prp, AtomInfo)]) --the union
instantiateUnion ags rep r =
    ( MPEvent
        { mpProps = bits ++ concat brAts  -- k bits, then every branch's block
        , mpLaw   = lawU  -- the big disjunction
        , mpObs   = obsU  -- everyone sees the bits
        , mpPts   = ptsU  -- xi of the union, Lemma 3.26
        }
    , bits
    , brAts
    , meta
    )
  where
    brs :: [MPEventSchema]
    brs = branchesOf rep

     -- how many branches the union has to distinguish
    m :: Int
    m = length brs

    -- We need k choice bits to distinguish m branches (at least 1, even for m=1, 
    -- so the layout is always uniform).
    k :: Int
    k = max 1 (ceilLog2 m)

    -- the first id of round r
    base :: Int
    base = 1000 * r

    -- The k choice-bit atoms
    bits :: [Prp]
    bits = [ P (base + j) | j <- [0 .. k - 1] ]

    -- The i-th offset is where branch (i+1)'s atoms begin, relative to base.
    -- scanl (+) k [a1, a2, ...] = [k, k+a1, k+a1+a2, ...]
    offsets :: [Int]
    offsets = scanl (+) k (map (length . esAtoms) brs)

    -- For each branch b, allocate consecutive ids
    brAts :: [[Prp]]
    brAts =
         -- branch b gets consecutive ids from its offset, one per declared atom name
        [ [ P (base + off + j) | j <- [0 .. length (esAtoms b) - 1] ]
        -- pair each branch with its offset
        | (b, off) <- zip brs offsets
        ]

    -- The encoding enc(i) from Section 3.2: the bits true in the binary code of branch i.
    -- Example (k=2): branch 1 -> enc 1 = [], branch 2 -> enc 2 = [bits!!0],
    --                branch 3 -> enc 3 = [bits!!1], branch 4 -> enc 4 = [bits!!0, bits!!1]
    enc :: Int -> [Prp]
    enc i = [ bits !! j | j <- [0 .. k - 1], odd ((i - 1) `div` (2 ^ j)) ]

    -- The branch selector of the thesis
    codeF :: Int -> Form
    codeF i = Conj
        -- Form version: the true bits of branch i's code ...
        (  [ PrpF c | c <- enc i ]
        -- ... and the negations of all the other bits
        ++ [ Neg (PrpF c) | c <- bits, c `notElem` enc i ]
        )

    -- The same code as a BDD, for use in the designated set BDD
    codeB :: Int -> Bdd
    codeB i = boolBddOf (codeF i)

    -- The inactive-branch forcing of Section 3.2
    inactF :: Int -> Form
    inactF i = Conj
        -- Form version: negate q ...
        [ Neg (PrpF q)
         -- ... for every atom q of every branch j other than i
        | (j, qs) <- zip [(1 :: Int) ..] brAts, j /= i, q <- qs
        ]

    -- The BDD version of inactF
    inactB :: Int -> Bdd
    inactB i = boolBddOf (inactF i)

    -- The union event law
    lawU :: Form
    lawU = Disj
        -- one disjunct per branch: code /\ branch law /\ padding
        [ Conj [codeF i, esLaw b (brAts !! (i - 1)), inactF i]
        | (i, b) <- zip [1 ..] brs  -- branches are 1-indexed, the list is not
        ]
      -- brs !! (i-1) is branch i's spec (0-indexed list, 1-indexed branches)
      -- brAts !! (i-1) gives branch i's fresh atoms

    -- The union designated set, following Lemma 3.26
    ptsU :: Bdd
    ptsU = disSet
        -- one disjunct per branch: code /\ designated /\ padding
        [ conSet [codeB i, esPts b (brAts !! (i - 1)), inactB i]
        -- same indexing as lawU
        | (i, b) <- zip [1 ..] brs
        ]

    -- Observability of the union
    obsU :: [(Agent, [Prp])]
    obsU =
        [ ( a
          -- for each agent a: all k choice bits, plus ...
          , bits ++ concat
                 -- ... a's part of branch i's atoms
                [ fromMaybe [] (lookup a (esObs b (brAts !! (i - 1))))
                 -- collected across all branches
                | (i, b) <- zip [1 ..] brs
                ]
          )
        -- one entry per agent
        | a <- ags
        ]

    -- Metadata for each union atom
    -- Choice bit j at round r is "c(j+1)@r" and is in block 0. Branch b's 
    -- atom at position (off+j) is named after its atom name, with "@r".
    meta :: [(Prp, AtomInfo)]
    meta =
        -- entries for the choice bits
        [ (c, AtomInfo r 0 j ("c" ++ show (j + 1) ++ "@" ++ show r))
        -- j = position among the bits
        | (j, c) <- zip [0 ..] bits
        ]
        -- followed by entries for all branch atoms:
        ++ concat
            -- branch atom q gets its declared name, tagged with the round
            [ [ (q, AtomInfo r 1 (off + j) (esAtoms b !! j ++ "@" ++ show r))
              -- j = position within the branch
              | (j, q) <- zip [0 ..] qs
              ]
            -- each branch with its atoms and block offset (extra offset dropped by zip3)
            | (b, qs, off) <- zip3 brs brAts offsets
            ]

{- | Decodes a 1-based branch index from the boolean values of its choice bits.

Bit @j@ contributes @2^j@ when it is true. Missing bits are treated as false.
-}
decodeBranch :: [Prp] -> [(Int, Bool)] -> Int
decodeBranch bits val = 1 + sum
    [ 2 ^ j
    -- j = bit position, c = the atom
    | (j, c) <- zip [(0 :: Int) ..] bits
    -- True iff this bit is set in val
    , fromMaybe False (lookup (unP c) val)
    ]


-- * The rho forms and the four readings

{- | Constructs the diamond and box rho forms 

* The first component holds when some admissible run reaches the goal.
* The second component holds when every admissible run reaches the goal.

-}
-- base vocab, structure, guard, goal formula to (rho_dia, rho_box)
rhoForms :: [Prp] -> KnowStruct -> Bdd -> Form -> (Bdd, Bdd)
-- keep the whole structure g for bddOf, and its vocabulary voc for the quantifier block
rhoForms baseV g@(KnS voc _ _) zeta goal =
     -- the two displayed projections: exists over guarded goal, forall over guard-implies-goal
    (existsSet quant (con zeta inner), forallSet quant (imp zeta inner))
  where
    -- The goal is translated against the current structure. This is where
    -- its knowledge operators are resolved against g
    inner :: Bdd
    inner = bddOf g goal

    -- Everything that is not base vocabulary can be quantified away and is thus
    -- in the quantifier block. At round 0 the block is empty and the forms are 
    -- guard and goal over the base.
    quant :: [Int]
    quant = map unP (voc \\ baseV)  -- list difference voc baseV, unwrap with unP


{- | The four readings of Theorem 3.12: worlds read universally
or existentially, events by box or diamond. The convention of the thesis is to
read worlds universally. Then, the box over the events is the conformant reading, 
according to which every outcome achieves the goal, and diamond over 
the events is the contingent reading,  where some outcome achieves the goal.  
-}
data Readings = Readings
    { strongAll :: !Bool  -- ^ from every initial state, every run
    , weakAll   :: !Bool  -- ^ from every initial state, some run
    , strongEx  :: !Bool  -- ^ from some initial state, every run
    , weakEx    :: !Bool  -- ^ from some initial state, some run
    } deriving stock (Eq, Show)

-- | Evaluate all four readings, given xi_S and the two rho forms.
readingsFrom :: Bdd -> (Bdd, Bdd) -> Readings
readingsFrom xiS (rD, rB) = Readings
    { strongAll = imp xiS rB == top  -- strongAll: xi_S -> rho_box is a tautology
    , weakAll   = imp xiS rD == top  -- weakAll: xi_S -> rho_dia is a tautology
    , strongEx  = con xiS rB /= bot  -- strongEx: xi_S /\ rho_box is satisfiable
    , weakEx    = con xiS rD /= bot  -- weakEx: xi_S /\ rho_dia is satisfiable
    }
-- top and bot are the tautology and contradiction BDDs.
-- imp a b = (neg a) \/ b; con = conjunction; == top checks validity.

-- * Pruning
{- | The doubled-vocabulary context of one structure, computed only once because
 it is shared by all pruning tests on it. This is the support of the law and
 the law's plain copy renamed by v-> 2v. The plain copy (even ids) 
is interleaved with the starred copy (odd ids) instead of using two blocks because
interleaving keeps the relabel maps monotone on sources that are sorted. This is needed 
by 'relabelSafe'. It also keeps the agreement clause linear as a BDD, in the case
where a block layout would make it exponential.
-}
data PruneCtx = PruneCtx
    { pcSupport  :: ![Int]  -- ^ the variables occurring in the law
    , pcLawPlain :: !Bdd    -- ^ the law under v -> 2v
    }

-- | Build the shared context once per structure, so that the per-atom tests
-- don't recompute the support or redo the even-copy relabelling every time
mkCtx :: KnowStruct -> PruneCtx
mkCtx (KnS voc law _) = PruneCtx
    { pcSupport  = allVarsOfSorted law  -- the vars the law actually mentions
     -- the plain copy: every id doubled; sorted so relabelSafe accepts the map
    , pcLawPlain = relabelSafe (sort [ (unP v, 2 * unP v) | v <- voc ]) law
    }

{- | Is the atom @q@ prunable, with back and forth required only for the
given audience (note that this can be the full audience)? 
Deleting @q@ merges all states that differ only in @q@, and 
an observer of @q@ does not necessarily win or lose a distinction by the merge.
This is what test Psi does (Proposition 5.6), by checking the validity per 
observer j: whenever a state t and a q-free valuation u' agree on j's remaining
observables, the extension of u' by t's value of @q@ is itself a state;
@q@ is prunable when Psi_j is valid for every observer j in the audience.  
We decide each Psi_j as one boolean validity over the interleaved doubled 
vocabulary of 'PruneCtx'.

We first check the following four sufficient conditions. 
They are the conditions described in Corollary 5.8, 
relativised to the audience, and one instance of its local determination case. 
Each of them is a special case of the validity, so the decisions are those 
of the plain test, but cheaper:

(0) no observer in the audience (this is case (i), relativised: to the 
    audience if appropriate). Then the empty conjunction of Psi's holds;

(1) @q@ outside the law's support: the law does not constrain @q@, this is
    and instance of case (iii);

(2) @q@ constant on the states: this is a determined atom, which, is locally 
    determined for every observer, so case (ii) applies;

(3) @q@ is a law-forced copy, or negated copy, of an atom w that every relevant
    observer of @q@ also observes: locally but not globally determined as in
    Example 5.20.

We only need the full check if none of the conditions apply. In this case,
the plain copy law is shared through the context, the cofactors are shared across
observers, and only the agreement clause is rebuilt per observer.
psiFor below is imp (hyp0 /\ agree) concl == top.
-}
prunable :: [Agent]     -- ^ audience: only these observers constrain the merge
    -> PruneCtx    -- ^ shared doubled-vocabulary data for this structure
    -> KnowStruct  -- ^ the structure being pruned
    -> Prp         -- ^ the candidate atom q
    -> Bool
prunable audience ctx kns@(KnS voc law obs) q =
       null observers                  -- (0)
    || unP q `notElem` pcSupport ctx   -- (1)
    || thT == bot || thF == bot        -- (2)
    || any copyOf shared               -- (3)
    || all psiFor observers            -- the full validity, per observer
  where
    -- who actually constrains the merge: observes q AND is in the audience
    observers :: [(Agent, [Prp])]
    observers = [ (j, os) | (j, os) <- obs, q `elem` os, j `elem` audience]

    -- The two cofactors of the law at q; both are q-free.
    thT, thF :: Bdd
    thT = restrict law (unP q, True)
    thF = restrict law (unP q, False)

    -- The observables that are shared by the relevant observer (without q)
    -- use foldr1 because guard (0) fails, so the list of observers is non-empty.
    shared :: [Prp]
    shared = foldr1 intersect [os | (_, os) <- observers] \\ [q]

    -- w is a copy, or anti-copy, of q when the law refutes their difference,
    -- or their sameness 
    copyOf :: Prp -> Bool
    copyOf w = con law (xor (var (unP q)) (var (unP w))) == bot  -- q <-> w forced
        || con law (equ (var (unP q)) (var (unP w))) == bot  -- q <-> not w forced

    keep :: [Prp]
    keep = sort (voc \\ [q])  -- everything except q, sorted for the relabel map

    -- renames every retained variable vv to a fresh starred copy:v -> 2v + 1, 
    -- applied only to q-free BDDs
    rn1 :: Bdd -> Bdd
    rn1 = relabelSafe (sort [ (unP v, 2 * unP v + 1) | v <- keep ])

    -- starred cofactors, computed once, reused by every observer
    rn1T, rn1F :: Bdd
    rn1T = rn1 thT
    rn1F = rn1 thF

    -- The hypothesis before per-observer agreement: t is a state (the plain
    -- law) and u' satisfies the q-projection of the law, which is the
    -- disjunction of the starred cofactors.
    -- t the original/current state, u' a prospective merged representative
    hyp0 :: Bdd
    hyp0 = con (pcLawPlain ctx) (dis rn1T rn1F)
    -- hyp0 = law(t) /\ (theta_T(u')\/theta_F(u'))
    -- So: t is a valid original/plain state, u'  is compatible with the projection
    -- of the law after forgetting q: it can be completed with either truth value of q

    -- The conclusion, split up wrt t's value of q, read from the plain copy 2q:
    -- extending u' by that value must satisfy the matching cofactor.
    concl :: Bdd
    concl = con
        (imp (var (2 * unP q)) rn1T)  -- t has q: u' plus q must be a state
        (imp (neg (var (2 * unP q))) rn1F)  -- t lacks q: u' plus not-q must be
    -- this is  (q(t) -> theta_T(u')) /\ (neg q(t) -> theta_F(u'))
    -- It requires that the value of q in the plain state t can be reinstated in u' 
    -- while preserving legality under the original law.

    -- Per-observer test
    psiFor :: (Agent, [Prp]) -> Bool
    psiFor (j, _) = imp (con hyp0 agree) concl == top
        -- for each relevant observer j, it checks the validity of
        -- hyp0(t, u') /\ agree_j(t,u')-> concl(t,u')
      where
        -- Plain and starred copies agree on j's observables other than q.
        -- The empty conjunction is top, so an observer with no other
        -- observables imposes agreement on nothing
        agree :: Bdd
        agree = conSet
            [ equ (var (2 * unP v)) (var (2 * unP v + 1))  -- plain = starred
            | v <- obsFor kns j \\ [q]   -- on all of j's observables except q
            ]
            -- agree_j(t,u') = /\_{v in O_j\{q}} (v(t) <-> v(u'))
    -- Intuition: If a relevant agent cannot distinguish a valid state t from a 
    -- prospective merged representative u' using their observables other than q, 
    --can u' always be completed with q's value from t and still satisfy the law?
    -- If yes, then removing q does not destroy any distinction that this observer 
    -- needs for the structure's valid-state behavior. Requiring all psiFor observers
    -- makes that condition hold for every relevant observer


{- | The reduct, denoted by the circled-minus operation in Chapter 5: 
@q@ is dropped from the vocabulary, and existentially projected out of the law, 
so the states of the reduct are exactly the states of the original with @q@ 
deleted, and removed from every observable set. We prune at the structure level. 
By Lemma 5.3 this agrees with reducing the event itself and then applying it.
-}
--  removes proposition q from all three parts of a KnowStruct: the vocabulary, 
-- the BDD law, and every agent's observable vocabulary.
pruneAtom :: KnowStruct -> Prp -> KnowStruct
pruneAtom (KnS voc law obs) q =
    KnS (voc \\ [q]) (exists_ (unP q) law) [ (j, os \\ [q]) | (j, os) <- obs ]
    -- (\\) is list difference: q deleted from the vocabulary and every O_j;
    -- exists_ projects it out of the law


-- * The pruned pipeline

{- | State of the iterative planning and pruning procedure.

This is the pruning pipeline of Chapter 5: round k updates by the step-k union, 
conjoins the guard's two new factors, then scans and prunes, projecting the 
guard by every removed atom. 
The invariant is that the guard implies the state law, so the guard
can never describe anything outside of the state space
-}
data Pipeline = Pipeline
    { plBase   :: !KnowStruct         -- ^ the initial structure
    , plStruct :: !KnowStruct         -- ^ G-hat, current and already pruned
    , plGuard  :: !Bdd                -- ^ zeta-hat, current, already projected
    , plRound  :: !Int                -- ^ how many rounds have been applied
    , plMeta   :: ![(Prp, AtomInfo)]  -- ^ metadata of all union atoms so far
    , plLog    :: ![String]           -- ^ the trace with the newest line first
    , plPeak   :: !Int                -- ^ the largest law BDD so far
    }

-- | Round 0: no actions yet, structure is the initial strucutre, guard is the 
-- state law
initPipeline :: KnowStruct -> Pipeline
initPipeline f = Pipeline
    { plBase   = f
    , plStruct = f
    , plGuard  = lawOf f  -- zeta_0 = theta_F: "run so far" just means state
    , plRound  = 0
    , plMeta   = []
    , plLog    = []
    , plPeak   = sizeOf (lawOf f)
    }

-- | infoOf looks up the metadata for an atom q in the pipeline's metadata table. 
-- If no metadata exists, it returns a fallback AtomInfo
infoOf :: Pipeline -> Prp -> AtomInfo
infoOf pl q =
    fromMaybe
        (AtomInfo (-1) 9 0 (show q)) -- round -1, block 9 as fallback
        (lookup q (plMeta pl))

{- | Ordering used to scan removable event atoms.

Candidates are only the event atoms. They are ordered by creation round, newer
rounds scanned first. Within a round, choice atoms are scanned before branch atoms, both
in their fixed enumeration order. Remaining atoms from earlier rounds follow,
again from newest to oldest.

This order removes later duplicate information before earlier copies. It is
therefore required for successive pruned rounds to become literally equal at a
fixed point, and for corresponding atoms to be tested consistently across
rounds.
-}
candOrder :: Pipeline -> [Prp]
candOrder pl = sortBy (comparing key) cands
  where
    cands :: [Prp]
    cands = vocabOf (plStruct pl) \\ vocabOf (plBase pl) --This selects the atoms introduced after the base structure

    -- Round descending (thats why the negation); then bits before branch atoms;
    -- then position within the round
    key :: Prp -> (Int, Int, Int)
    key q = (negate (aiRound ai), aiBlock ai, aiIdx ai)
      where
        ai :: AtomInfo
        ai = infoOf pl q

{- | Performs one planning round.
instantiates the repertoire as a union event, applies that event to the current structure,
updates the guard, logs unpruned result, optionally runs pruning
-}
stepPipeline :: Bool ->  --whether to prune after the round
    [Agent] ->  -- the audience for the scan
    [Agent]->  -- all agents of the problem, for the union's observables
    Repertoire ->
    Pipeline ->
    Pipeline
stepPipeline doPrune pruneAgs ags rep pl
-- the returned pipeline is extended, if pruning is disabled 
    | doPrune = pruneToFixpoint pruneAgs extended
    -- the result of repeatedly pruning extended until no more candidates can be removed, 
    -- if pruning is enabled
    | otherwise = extended
  where
    r :: Int
    --The next round number is one greater than the round stored in the incoming pipeline.
    r = plRound pl + 1

    -- The bits and per-branch atoms are only needed at extraction time, so
    -- they are ignored here.
    (u, _, _, meta) = instantiateUnion ags rep r
    --instantiateUnion builds the event union for round r.
    -- u is the resulting MPEvent. meta is the metadata for the fresh choice and branch
    -- atoms introduced in this round

    (g', lawB) = applyEvent (plStruct pl) u
    --This applies the new event u to the current epistemic/knowledge structure:
    -- g' is the expanded KnowStruct, lawB is the BDD translation of the event law against the previous structure
    -- so law(g')= law(g) /\ lawB

    -- This takes the old Pipeline record pl and replaces only the fields listed inside; 
    -- all other fields remain unchanged.
    extended :: Pipeline
    extended = pl
        { plStruct = g'  --Store the expanded knowledge structure
        -- Guard_r = Guard_{r-1} /\ mpPts(u) /\ lawB
        , plGuard  = con (plGuard pl) (con (mpPts u) lawB)  -- the guard recursion
        , plRound  = r  --	Record that one further round has happened
        , plMeta   = meta ++ plMeta pl 
        , plPeak   = max (plPeak pl) (sizeOf (lawOf g'))  --Maintain the greatest observed law-BDD size
        -- max of the previous peak size and the current unpruned structure law's BDD size
        -- Important: this is before optional pruning
        , plLog    = logLine : plLog pl  --Prepend this round's log entry

        }

    -- vocab and law size of the fresh, unpruned round
    logLine :: String
    logLine = "round " ++ show r ++ ": vocab "
        ++ show (length (vocabOf g')) ++ ", law size "
        ++ show (sizeOf (lawOf g'))

-- | Passes are repeated until one pass removes nothing
-- a removal can lead to the removal of another atom
pruneToFixpoint :: [Agent] -> Pipeline -> Pipeline
pruneToFixpoint audience pl
    -- stopping condition: If something was removed, run another pass on the smaller pipeline.
    | changed = pruneToFixpoint audience pl'
    -- If a pass removes nothing, return its result. Since no candidate was prunable 
    -- under the current structure, this is the fixed point for the given scan rule and audience.
    | otherwise = pl'
  where
    (pl', changed) = prunePass audience pl


{- | Performs one left-to-right greedy pruning pass.

For each candidate atom, the function tests whether it can be removed from the
current structure. If so, it removes it, rebuilds the pruning context,
and continues with the remaining candidates.

Returns the updated pipeline and whether at least one atom was removed.
-}
prunePass :: [Agent] -> Pipeline -> (Pipeline, Bool)
-- pl0: the initial pipeline
-- mkCtx (plStruct pl0): a PruneCtx computed from the initial structure
-- False: no atom has been removed yet
-- candOrder pl0: the oredered list of non-base candidates
prunePass audience pl0 = go pl0 (mkCtx (plStruct pl0)) False (candOrder pl0)
  where
    go :: Pipeline -> PruneCtx -> Bool -> [Prp] -> (Pipeline, Bool)
    -- end of the scan. When no candidates remain, return the current (possibly pruned)
    -- pipeline; return whether any deletion occurred during this pass
    --_ means the context is irrelevant once there is nothing left to test.
    go pl _ changed [] = (pl, changed)
    -- test the next candidate: For the next candidate q: If prunable ... q is true, 
    -- prune it and continue. Otherwise, leave the pipeline/context unchanged and move on.
    go pl ctx changed (q : qs)
        | prunable audience ctx (plStruct pl) q =
            go pl' (mkCtx g') True qs  -- fresh context: the structure shrank by q so the vocab is 
            --smaller, the law has been existentially abstracted, its BDD support may have changed
        | otherwise = go pl ctx changed qs  -- a later pass may still free q
      where
        -- If q is prunable
        g' :: KnowStruct
        g' = pruneAtom (plStruct pl) q

        -- then update the pipeline consistently
        pl' :: Pipeline
        pl' = pl
            { plStruct = g'  --Store the structure with q removed
            , plGuard  = exists_ (unP q) (plGuard pl)  -- Remove q from the cumulative guard too
            , plPeak   = max (plPeak pl) (sizeOf (lawOf g'))   -- 	Preserve the largest BDD-law size encountered
            , plLog    = ("  pruned " ++ aiName (infoOf pl q)) : plLog pl  --Add a readable pruning log entry
            }


{- | Tests whether two pipeline states are equal for the purpose of detecting
a literal fixed point (Definition 5.35).
The states must have the same vocabulary, state law, observability relation,
and guard. BDD equality is used directly because BDDs have canonical forms.
Observability is compared after sorting agents and their observable atoms.
-}
samePipeline :: Pipeline -> Pipeline -> Bool
samePipeline a b =
       sort (vocabOf (plStruct a)) == sort (vocabOf (plStruct b)) -- same atoms (sorted first)
    && lawOf (plStruct a) == lawOf (plStruct b)  -- same law
    && nrm (plStruct a) == nrm (plStruct b)  -- same observables, normalised
    && plGuard a == plGuard b  -- same guard
  where
    -- Per agent the sorted observable set, agents sorted
    nrm :: KnowStruct -> [(Agent, [Prp])]
    nrm k = sort [ (i, sort (obsFor k i)) | i <- agentsOf k ]



-- * The link certificate: greatest guard-compatible symbolic bisimulation

{- | The largest audience bisimulation of Definition A.12, Remark A.15 for the shared
vocabulary @v@ between two structures, with forth and back required only for
the agents of the audience. It is computed as a BDD over four interleaved
copies of a compacted id space: the atom of rank p uses 4p for its
left-source copy, 4p + 1 for right-source, 4p + 2 for left-target and
4p + 3 for right-target, so that every relabel map below is monotone on
sorted sources. The computation is the greatest-fixpoint refinement as in Lemma 4.21(ii):
we start from statehood and propositional agreement on @v@, intersect with
forth and back, andrepeat until the BDD is fixed.
-}
largestBisim :: [Agent] -> [Prp] -> KnowStruct -> KnowStruct -> Bdd
-- agsB: agents whose indistinguishability relations must be preserved.
-- v: proposition atoms on which related states must agree.
-- g1, g2: the two knowledge structures.
-- Result: a BDD over paired/copy variables, representing a binary relation between a g1 state and a g2 state.
-- beta0 is the base relation, beta0(s,t) = theta_1(s) /\ theta_2(t) /\ /\_{p in v} (p(s) <-> p(t))
-- So initially, pairs are allowed only if: the left component is a legal g1 state; 
-- the right component is a legal g2 state; they agree on every atom in v.
largestBisim agsB v g1@(KnS voc1 th1 _) g2@(KnS voc2 th2 _) = go beta0
  where
    -- the union of proposition IDs used by either structure, sorted and deduplicated.
    allIds :: [Int]
    allIds = sort (nub (map unP (voc1 ++ voc2)))

    -- maps each actual proposition ID to its compact rank in this joint vocabulary. 
    -- total for IDs that occur in voc1 or voc2; the fallback 0 should be unreachable under the intended invariant.
    posOf :: Int -> Int
    posOf n = fromMaybe 0 (lookup n (zip allIds [0 ..]))

    -- the four copies of atom rank p: left/right source states s, t; left/right target or successors s', t'
    lsOf, rsOf, ltOf, rtOf :: Int -> Int
    lsOf n = 4 * posOf n       -- left source
    rsOf n = 4 * posOf n + 1   -- right source
    ltOf n = 4 * posOf n + 2   -- left target
    rtOf n = 4 * posOf n + 3   -- right target

    -- move each original BDD over voc1 or voc2 into one of the four variable blocks
    rnLS, rnRS, rnLT, rnRT :: Bdd -> Bdd
    rnLS = relabelSafe (sort [ (unP p, lsOf (unP p)) | p <- voc1 ])
    rnRS = relabelSafe (sort [ (unP p, rsOf (unP p)) | p <- voc2 ])
    rnLT = relabelSafe (sort [ (unP p, ltOf (unP p)) | p <- voc1 ])
    rnRT = relabelSafe (sort [ (unP p, rtOf (unP p)) | p <- voc2 ])
    -- Example: th1LT = rnLT th1, th2RT = rnRT th2

    -- Rebase the relation from source copies to target copies, to use
    -- inside forth and back
    srcToTgt :: Bdd -> Bdd
    srcToTgt = relabelSafe (sort
        (  [ (lsOf (unP p), ltOf (unP p)) | p <- voc1 ]
        ++ [ (rsOf (unP p), rtOf (unP p)) | p <- voc2 ]
        ))

    -- the two laws in target position, used inside forth and back
    -- the target valuations are valid states of their respective structures:
    th1LT, th2RT :: Bdd
    th1LT = rnLT th1
    th2RT = rnRT th2

    -- the quantifier blocks: all left targets, all right targets
    ltVars, rtVars :: [Int]
    ltVars = map (ltOf . unP) voc1
    rtVars = map (rtOf . unP) voc2

    -- Agreement of two copies on a set of atoms. Same observables is 
    -- what "j-successor" means, so this is how the epistemic step is encoded
    eqOn :: (Int -> Int) -> (Int -> Int) -> [Prp] -> Bdd
    eqOn ofL ofR ps = conSet [ equ (var (ofL (unP p))) (var (ofR (unP p))) | p <- ps ]
    -- In a knowledge structure, a j-accessible successor is a legal state that agrees with 
    -- the source state on the atoms observed by agent j. This creates equality constraints across copies.
    -- Example: eqOn lsOf ltOf (obsFor g1 j) denotes /\_{p in O_j^1}(p(s) <-> p(s')).
    -- Together with th1LT, this says s' is a legal state in g1 that agent j cannot distinguish from s.

    -- The start: both sides are states, and they agree propositionally on v
    beta0 :: Bdd
    beta0 = conSet
        (  [rnLS th1, rnRS th2]  -- both components are states of their side
        ++ [ equ (var (lsOf (unP p))) (var (rsOf (unP p))) | p <- v ]  -- agree on v
        )

    -- Forth for j: every j-successor on the left has a j-successor on the
    -- right that the relation links. every left-target
    -- state that is a state and agrees with the left source on j's
    -- observables has some right-target partner (state, agrees with the
    -- right source on j's observables) that the shifted relation btaT links them
    forthFor :: Bdd -> Agent -> Bdd
    forthFor btaT j = forallSet ltVars $ imp
        (con th1LT (eqOn lsOf ltOf (obsFor g1 j)))
        (existsSet rtVars (conSet [th2RT, eqOn rsOf rtOf (obsFor g2 j), btaT]))
        -- BDD encoding of \forall s' (theta_1(s') /\ s ~_j^1 s' -> \exists t' (theta_2(t') /\ t ~_j^2 t' /\ beta(s', t')))
        -- Every j-indistinguishable successor s' of the left source state must have some j-indistinguishable successor 
        -- t' of the right source state such that (s', t') remains in the relation.
        -- ltVars = map (ltOf . unP) voc1; rtVars = map (rtOf . unP) voc2 quantify all left or right target variables, respectively

    -- Back is symmetric.    
    backFor :: Bdd -> Agent -> Bdd
    backFor btaT j = forallSet rtVars $ imp
        (con th2RT (eqOn rsOf rtOf (obsFor g2 j)))
        (existsSet ltVars (conSet [th1LT, eqOn lsOf ltOf (obsFor g1 j), btaT]))
        -- BDD encoding of \forall t' (theta_2(t') /\ t ~_j^2 t' -> \exists s' (theta_1(s') /\ s ~_j^2 s' /\ beta(s', t')))

    -- One refinement step. The relation can only shrink, so bot is final, and
    -- equality with the previous round means that the fixpoint is reached
    go :: Bdd -> Bdd
    go bta
        | bta' == bot = bot  --no candidate related pairs remain.
        | bta' == bta = bta  -- no more pairs are removed, so the greatest fixed point has been reached.
        | otherwise = go bta'
      where
        -- shift beta to the targets
        btaT :: Bdd
        btaT = srcToTgt bta
        -- srcToTgt = relabelSafe [ ls(p) |-> lt(p), rs(p) |->  rt(p) ]
        -- turns beta(s,t) into beta (s', t')
        -- Without this renaming, bta would incorrectly relate the original source 
        -- states inside the successor-matching condition.

        bta' :: Bdd
        bta' = conSet
            (bta : concat [ [forthFor btaT j, backFor btaT j] | j <- agsB ])
            -- beta_{n+1} + beta_n /\ /\_{j in A} (Forth_j(beta_n) /\ Back_j(beta_n))
            -- Each iteration can only remove pairs, never add them: beta_{n+1} \subseteq beta_n


{- | The link certificate of Definition A.12: the largest audience bisimulation
for the base vocabulary must relate every guard-state of either side to a guard-
state of the other. It is checked as two validities against the relation. A link 
between consecutive stages fixes all audience readings from that horizon on.
once a link exists it persists. By Remark A.15,Psi checks whether a given projection
is a link one atom down, the literal fixpoint checks whether the identity relation 
is a link between stages, and this refinement asks whether any link exists at all.
-}
-- checks whether the guarded states of two pipeline stages are linked by a total 
-- bisimulation—for the chosen audience agsB and base vocabulary v
-- It returns True exactly when every state allowed by either stage’s guard has at 
-- least one bisimilar guarded counterpart in the other stage.
linkCert :: [Agent] ->  -- the audience
    [Prp] ->  -- the base vocabulary 
    (KnowStruct, Bdd) ->  -- the later stage, with its guard (g1, z1)
    (KnowStruct, Bdd) ->   --the earlier stage, with its guard (g2, z2)
    Bool  --whether there is a link 
linkCert agsB v (g1@(KnS voc1 _ _), z1) (g2@(KnS voc2 _ _), z2) =
    -- total bisimulation requires coverage in both directions: every state on the 
    --left relates to some state on the right, and every state on the right relates 
    -- to some state on the left.
    -- |= z_1(s) -> exists t (beta(s,t) /\ z_2(t)). Every left/later state satisfying guard 
    -- z1 is bisimilar to at least one right/earlier state satisfying guard z2.
    -- rnLS z1 is the later-stage guard z1, renamed to left-source vars.
    -- con bta (rnRS z2) is a bisimilar right counterpart that lies in the earlier guard
       imp (rnLS z1) (existsSet rsVars (con bta (rnRS z2))) == top   -- left to right
       -- |= z_2(t) -> exists s (beta(s,t) /\ z_1(s)).
    && imp (rnRS z2) (existsSet lsVars (con bta (rnLS z1))) == top  -- and back
  where
    -- the largest candidate bisim relation between g1 and g2 over the two source-copy vocabs
    bta :: Bdd
    bta = largestBisim agsB v g1 g2
    -- this imposes: state legality on both sides, agreement on atoms in v, forth and
    -- back conditions for every agent in agsB
    -- thus, there is no need to construct another relation. If this maximal relation fails
    -- to link the guarded sets totally, then no smaller bisim can. 

    -- recomputes the same compact proposition ranks used by largestBisim:
    allIds :: [Int]
    allIds = sort (nub (map unP (voc1 ++ voc2)))

    posOf :: Int -> Int
    posOf n = fromMaybe 0 (elemIndex n allIds)

    -- The same source copies as in 'largestBisim', so that the guards and the
    -- relation are about the same variables.
    rnLS, rnRS :: Bdd -> Bdd
    rnLS = relabelSafe (sort [ (unP p, 4 * posOf (unP p)) | p <- voc1 ])
    rnRS = relabelSafe (sort [ (unP p, 4 * posOf (unP p) + 1) | p <- voc2 ])

    -- list the BDD variables encoding the left and right source state, respectively.
    lsVars, rsVars :: [Int]
    lsVars = [ 4 * posOf (unP p) | p <- voc1 ] -- quantify rsVars to project a relation over pairs (s,t) down to its left domain.
    rsVars = [ 4 * posOf (unP p) + 1 | p <- voc2 ]  -- quantify lsVars to project it down to its right range.
    -- dom(beta \cap (w_1 x Z_2)) \supseteq Z_1 and ran(beta \cap (Z_1 x W_2)) \supseteq Z_2

    -- This fuinction certifies (G_1, z_1) ~_{agsB, v} (G_2,z_2)
    -- where the relation is atom-preserving only for v; epistemically bisimulating for agents in agsB;
    -- total on the states selected by z1 and z2. Consequently, corresponding guarded states 
    -- satisfy the same epistemic formulas built from the vocabulary v and the agents agsB, 
    -- by bisimulation invariance.


-- * Variants, outcomes, results

-- | The four search variants
data Variant
    = VTree   -- ^ tree
    | VUnion  -- ^ union, no pruning
    | VPrune  -- ^ pruning, literal fp
    | VFull   -- ^ pruning relative to audience, link certificate
    deriving stock (Eq, Show)

-- | The long names used for the reports
variantName :: Variant -> String
variantName VTree  = "tree: one structure per action sequence"
variantName VUnion = "union: composed pipeline, no pruning"
variantName VPrune = "prune: union + pruning (full Psi, literal fixpoint)"
variantName VFull  = "full: union + audience pruning + link certificate"


-- | The command-line names of the variants
variantsByName :: [(String, Variant)]
variantsByName =
    [ ("tree",  VTree)
    , ("union", VUnion)
    , ("prune", VPrune)
    , ("full",  VFull)
    ]

{- | A plan that was extracted from a satisfying assignment.

Each entry represents one planning round. It contains the selected action's
name and the truth values that are assigned to the  event atoms of that action
-}
type PlanTrace = [(String, [(String, Bool)])]


-- | Result of a planning search.
data Outcome
    = PlanFound !Int ![(State, Maybe PlanTrace, Bool)]
      -- ^ A plan was found at this horizon. Each entry contains an initial
      -- state, an optional extracted plan, and whether independent replay
      -- validated that plan.
    | NoPlan !Int !String
      -- ^ No plan exists at this horizon; the string gives the certificate
    | Exhausted !Int
      -- ^ The horizon limit was reached without finding a plan or proving
      -- its absence.
    deriving stock (Show)

-- | Result returned by each search variant.
data SearchResult = SearchResult
    { srOutcome :: !Outcome
    , srLog     :: ![String]           -- ^ log in chronological order
    , srHist    :: ![(Int, Readings)]  -- ^ readings recorded at each horizon
    , srSizes   :: ![(Int, Int, Int)]  -- ^ Per-horizon size data: horizon, vocabulary size, and state-law BDD siz
    , srPeak    :: !Int                -- ^ Largest law BDD encountered during the search.
    }


-- * The pipeline search

{- | Searches for a plan using the composed public-choice construction.

This implementation is used by the union, prune, and full variants. At each
horizon, it computes the rho forms of the current pipeline state and evaluates
the accumulated weak reading: every designated initial state must satisfy the
disjunction of the diamond rho forms obtained up to that horizon.

The search first checks if there is a literal fixed point between consecutive pipeline
states. In the full variant, it additionally tries to find a link.
 A link search is only attempted when the rho forms at the current and
previous horizons agree, because agreement is necessary for it.

Link search attempts are tried following the schedule @1, 2, 4, 8, ...@. 
-}
searchPipeline :: Variant ->  --'VUnion', 'VPrune' or 'VFull' 
    Int ->  -- the horizon cap
    [Agent] ->  -- agents of the problem 
    KnowStruct ->  -- the initial structure 
    [State] ->  -- the designated initial states 
    Repertoire ->
    Form ->  -- goal formua 
    SearchResult
searchPipeline variant maxR ags f bigS rep goal =
    loop (initPipeline f) [] [] [] Nothing  -- initial call. 
    -- ^ begins at round 0 with: the initial pipeline built from f; no previously 
    -- computed diamond BDDs; empty histories and size data; no preceding pipeline stage.
  where
    doPrune, doSem :: Bool
    doPrune = variant /= VUnion  -- union is the only variant that never prunes
    doSem = variant == VFull   -- and full is the only one that tries the link

    --  turns the designated initial states bigS into the BDD xi_S, over the original/base vocabulary of f.
    xiS :: Bdd
    xiS = xiOf (vocabOf f) bigS  -- xi_S over the base vocabulary

    -- The audience, as described in Section A.6: the goal formula
    -- names the agents whose knowledge we care about, and the event laws 
    -- name those agents whose information the action tests. 
    --- The laws are instantiated at throwaway atoms only so we can
    -- read the agent names off, but those ids are never in any structure.
    live :: [Agent]
    live = nub $ agentsInForm goal ++ concat
        -- concat the agents named in the event laws of repertoire branches.
        [ agentsInForm (esLaw b [ P (900000 + i) | i <- [0 .. length (esAtoms b) - 1] ])
        | b <- branchesOf rep
        ]

    -- who the scan protects: everybody, unless we are in the audience variant
    pruneAgs :: [Agent]
    pruneAgs
        | variant == VFull = live  -- VFull, pruning preserves distinctions for the audience from live
        | otherwise = ags  -- for ordinary pruning, it protects all agents

    -- [Bdd] is the diamond of every horizon so far
    --Maybe (Pipeline, (Bdd, Bdd)) is the previous stage, with its forms
    loop :: Pipeline -> [Bdd] -> [(Int, Readings)] -> [(Int, Int, Int)]
         -> Maybe (Pipeline, (Bdd, Bdd)) -> SearchResult
    -- Order: success first, then the certificates, then the
    -- horizon cap, and only then another round
    loop pl dias hist sizes prev
        | reached = finish (PlanFound (plRound pl) [ planFor s dias' | s <- bigS ])
        -- ^ this is |= xi_S -> \/_{h=0}^r rho_h^diamond, i.e. every designated initial state 
        -- satisfies the weak/diamond condition at at least one horizon up to the current round.
        | otherwise = case prev of
            -- stages literally equal: Definition 5.35 fired, and by
            -- Theorem 5.36 nothing will ever change again
            Just (p, _) | doPrune, samePipeline p pl ->
                finish (NoPlan (plRound pl - 1) "literal fixpoint")
            Just (p, (pD, pB)) | doSem
                , let r = plRound pl
                , r .&. (r - 1) == 0   -- power of two: rounds 1,2,4,8 (Remark A.15)
                , rD == pD, rB == pB  -- free precheck: current and previous rho_dia and rho_box BDDs are already identical
                -- ^ when this is not the case, we avoid an expensive bisimulation calculation 
                , linkCert live (vocabOf f)
                -- ^ establishes a guarded total bisimulation link between the current/later 
                -- and previous/earlier structures, for: the live audience live; the base vocabulary vocabOf f.
                    (plStruct pl, plGuard pl)   -- later stage
                    (plStruct p, plGuard p) ->  -- earlier stage
                finish (NoPlan (plRound pl - 1) "link certificate")
                -- ^ If all hold, the system concludes that no later horizon can change the relevant answer and reports
            _ | plRound pl >= maxR -> finish (Exhausted (plRound pl))
              -- ^ If there is no success/certificate and the cap has been reached,the result is inconclusive give up :(
              | otherwise -> loop  -- no verdict yet: do one more round
                    (stepPipeline doPrune pruneAgs ags rep pl)   -- apply one more round, optionally prune to a fp
                    dias' hist' sizes' (Just (pl, (rD, rB)))  -- preserve all current historical data, save the current pipeline and rho-forms as prev
      where
        -- At the current pipeline stage, this computes:
        -- rD: the diamond/weak projection, there is a guarded continuation satisfying goal; 
        -- rB: the box/strong projection, all guarded continuations satisfy goal.
        (rD, rB) = rhoForms (vocabOf f) (plStruct pl) (plGuard pl) goal

        -- stores the diamond BDD for each horizon so far.
        dias' :: [Bdd]
        dias' = dias ++ [rD]

        -- records the four all/existential and weak/strong readings at the current round.
        hist' :: [(Int, Readings)]
        hist' = hist ++ [(plRound pl, readingsFrom xiS (rD, rB))]

        -- what the log and the summary table report afterwards: (round number, vocabulary size, law-BDD size)
        sizes' :: [(Int, Int, Int)]
        sizes' = sizes ++
            [ ( plRound pl
              , length (vocabOf (plStruct pl))
              , sizeOf (lawOf (plStruct pl))
              )
            ]

        -- The accumulated weak criterion of the bounded iterate.
        -- Theorem 5.36: valid iff a plan exists within the current horizon.
        reached :: Bool
        reached = imp xiS (disSet dias') == top

        finish :: Outcome -> SearchResult
        finish out = SearchResult
            { srOutcome = out  -- the plan/no-plan/exhaustion outcome;
            , srLog     = reverse (plLog pl)  -- Because log entries were prepended with :, 
            -- ^ the function reverses them before returning to restore chronological order
            , srHist    = hist'  -- all recorded readings;
            , srSizes   = sizes'  -- per-round vocabulary and BDD-law sizes;
            , srPeak    = plPeak pl  --the peak BDD-law size reached during construction or pruning.
            }

    -- planFor finds the first horizon at which that state satisfies a stored diamond BDD:
    -- the trace is then read off the unpruned copy, because pruning can be used
    -- only for the readings, not for witnesses, as the scan might have
    -- deleted the choice bits a witness decodes.
    -- So j is the shallowest horizon that works for s.
    planFor :: State -> [Bdd] -> (State, Maybe PlanTrace, Bool)
    planFor s dias =
        case [ j | (j, d) <- zip [0 ..] dias, evaluateFun d (\n -> P n `elem` s) ] of
             -- all horizons whose diamond is true at s, evaluateFun just plugs
            -- the state in as a boolean valuation
            [] -> (s, Nothing, False)  -- can't happen once reached held
            -- call extractTrace on the unpruned construction because pruning may have 
            --removed choice-bit atoms needed to decode the selected branch/action trace.
            (j : _) -> case extractTrace ags f rep goal j s of
                 -- j is the shallowest horizon that works for this s
                Nothing -> (s, Nothing, False)  -- extraction failed: shows FAIL
                Just tr -> (s, Just tr, verifyTrace ags rep goal f s tr)
                -- ^ independently replays the extracted trace as a correctness check.


-- * The tree search

{- | A node of the naive view in Remark 3.44.
Building the tree gives one natural-update sequence per path, each with its 
own structure and guard, so in one tree there are m^d structures at depth d, 
while at the composed view there is only one. 
Per depth we give the disjunction of the per-path diamonds, which by  
Corollary 3.50 is equal to the composed view's diamond at the same horizon, 
so the success criterion is identical for both variants. The reported box is 
the disjunction of the per-path boxes. This is a different quantity from the 
composed view's single box, and it is vacuously true at states where a path 
is inapplicable, so it is shown for information only.
-}
data TreeNode = TreeNode
    { tnStruct :: !KnowStruct  --The knowledge structure obtained after following this action path
    , tnGuard  :: !Bdd  --The cumulative guard/designated condition along the path
    , tnRounds :: ![(MPEventSchema, [Prp])]  -- The actions chosen so far, together with their round-specific fresh atoms
    -- tnRounds is "oldest first", so it can later be decoded directly into a PlanTrace.
    }

-- | A single-branch event for round @r@, without choice atoms: in the naive
-- view each natural-update sequence is its own branch, so no public choice
-- is needed.
-- This takes a branch schema and turns it into a one-branch MPEvent:
branchEvent :: Int -> MPEventSchema -> MPEvent
branchEvent r b = MPEvent
    { mpProps = qs
    , mpLaw   = esLaw b qs
    , mpObs   = esObs b qs
    , mpPts   = esPts b qs
    }
  where
    -- Round r has the block from 1000r onwards, as in the union. Nodes of the
    -- same depth reuse the ids, which is harmless across separate structures.
    qs :: [Prp]
    qs = [ P (1000 * r + j) | j <- [0 .. length (esAtoms b) - 1] ]

-- | Breadth-first search over the naive view (tree). This cannot certify
-- impossibility. The search either finds a plan or runs out of horizon.
-- Int is the horizon cap, KnowStruct the initial structure, [State] the 
-- designated initial states, and Form the goal formula
searchTree :: Int -> [Agent] -> KnowStruct -> [State] -> Repertoire -> Form
           -> SearchResult
searchTree maxR ags f bigS rep goal =
    go 0 [TreeNode f (lawOf f) []] [] [] [] [] []
     -- ^ At depth 0: the frontier contains only the initial structure f; 
     -- its guard is the initial state law lawOf f; there is no action history;
     -- the accumulators for discovered nodes, diamond BDDs, readings, sizes, and logs are empty.
  where
    -- xiS constructs the BDD describing the designated initial states.
    xiS :: Bdd
    xiS = xiOf (vocabOf f) bigS  -- same xi_S as in the pipeline search

    -- the vocabulary to which every rhoForms result is projected
    baseV :: [Prp]
    baseV = vocabOf f  -- the tree quantifies down to this a lot, so we need it

    -- Int is the current depth
    -- [TreeNode] is the frontier: all nodes representing action sequences of length d
    -- [(TreeNode, Bdd)] is every node encountered so far, paired with its diamond BDD
    -- [Bdd] is the per-depth disjoined diamonds
    go :: Int -> [TreeNode] -> [(TreeNode, Bdd)]  -> [Bdd] -> [(Int, Readings)] 
            -> [(Int, Int, Int)] -> [String] -> SearchResult
    -- dias: One disjoined diamond BDD per depth; hist: per-depth strong/weak readings;
    -- sizes: per-depth max vocab/law-BDD sizes; logs: per-depth textual log entries
    go d frontier found dias hist sizes logs
        | reached = SearchResult   -- success: same shape as the pipeline result
            { srOutcome = PlanFound d [ planFor s found' | s <- bigS ]
            , srLog     = logs'
            , srHist    = hist'
            , srSizes   = sizes'
            , srPeak    = peak
            }
        | d >= maxR = SearchResult  -- out of horizon, the tree can't say more
            { srOutcome = Exhausted d
            , srLog     = logs'
            , srHist    = hist'
            , srSizes   = sizes'
            , srPeak    = peak
            }
        | otherwise = go  -- one level deeper
            (d + 1)
            (concatMap (expand (d + 1)) frontier)  -- every child of every node
            found'
            dias'
            hist'
            sizes'
            logs'
      where
         -- rho forms of every frontier node, computed here and reused below
         -- the BDD tuple is (diamondBDD, boxBDD)
        pairs :: [(TreeNode, (Bdd, Bdd))]
        pairs =
            [ (nd, rhoForms baseV (tnStruct nd) (tnGuard nd) goal)
            | nd <- frontier
            ]

        rD, rB :: Bdd
        rD = disSet [ dB | (_, (dB, _)) <- pairs ]   -- per-depth diamond
        rB = disSet [ bB | (_, (_, bB)) <- pairs ]   -- disjoined boxes, info only
        -- rD_d + \/_{node at depth d} rho^dia_node. 

        found' :: [(TreeNode, Bdd)]
        found' = found ++ [ (nd, dB) | (nd, (dB, _)) <- pairs ]

        dias' :: [Bdd]
        dias' = dias ++ [rD]

        hist' :: [(Int, Readings)]
        hist' = hist ++ [(d, readingsFrom xiS (rD, rB))]

        -- maxima, for log and summary table
        vmax, lmax :: Int
        vmax = maximum [ length (vocabOf (tnStruct nd)) | nd <- frontier ]
        lmax = maximum [ sizeOf (lawOf (tnStruct nd)) | nd <- frontier ]

        sizes' :: [(Int, Int, Int)]
        sizes' = sizes ++ [(d, vmax, lmax)]

        logs' :: [String]
        logs' = logs ++
            [ "depth " ++ show d ++ ": " ++ show (length frontier)
                ++ " structures, max vocab " ++ show vmax
                ++ ", max law size " ++ show lmax
            ]

        -- weak
        reached :: Bool
        reached = imp xiS (disSet dias') == top

        peak :: Int
        peak = maximum [ l | (_, _, l) <- sizes' ]  -- non-empty: depth 0 is in

    -- for every node all their neighbors reachable in 1 step
    expand :: Int -> TreeNode -> [TreeNode]
    expand r nd =
        [ TreeNode
            { tnStruct = g'
            , tnGuard  = con (tnGuard nd) (con (mpPts t) lawB)  -- guard, per path
            , tnRounds = tnRounds nd ++ [(b, mpProps t)]  -- remember the path
            }
        | b <- branchesOf rep
        , let t = branchEvent r b  -- this branch, instantiated at round r
        , let (g', lawB) = applyEvent (tnStruct nd) t
        ]

    -- The accumulator grows in the order of depth, so the first hit is the
    -- witness with the least depth.  
    -- The trace is decoded from a satisfying assignment of that node's guarded 
    -- and translated goal, restricted to the initial state.
    planFor :: State -> [(TreeNode, Bdd)] -> (State, Maybe PlanTrace, Bool)
    planFor s found =
        case [ nd | (nd, dB) <- found, evaluateFun dB (\n -> P n `elem` s) ] of
            -- the recorded nodes whose diamond is true at s, oldest first
            [] -> (s, Nothing, False)
            (nd : _) ->
                case anySatWith (map unP (vocabOf (tnStruct nd))) (goalHere nd) of
                    -- one satisfying assignment of guard /\ goal /\ "we are at s"
                    Nothing -> (s, Nothing, False) -- no witness: count as failed
                    Just v ->
                        let tr = decodePath nd v
                        in (s, Just tr, verifyTrace ags rep goal f s tr)
      where
        -- this node's guard, the goal translated at this node, and s pinned
        -- down: satisfying assignments are exactly the runs of this path from s
        goalHere :: TreeNode -> Bdd
        goalHere nd =
            conSet [tnGuard nd, bddOf (tnStruct nd) goal, cubeOf baseV s]

        -- the path is stored in tnRounds, so decoding is basically reading each
        -- branch's atoms out of the assignment, for each round
        decodePath :: TreeNode -> [(Int, Bool)] -> PlanTrace
        decodePath nd v =
            [ ( esName b
              , [ (nm, fromMaybe False (lookup (unP q) v))  -- value of atom nm
                | (nm, q) <- zip (esAtoms b) qs  -- declared name <-> fresh atom
                ]
              )
            | (b, qs) <- tnRounds nd
            ]


-- * Plan extraction and the independent check

{- | Extracts a plan witness at horizon @j@.

The function rebuilds the unpruned pipeline through horizon @j@ and obtains a
satisfying assignment for the selected initial state. It decodes each round's
choice bits as an action and its branch atoms as event-atom values.

this uses the unpruned pipeline, because the pruning might delete the 
atoms that are needed for decoding.
-}
extractTrace :: [Agent] -> KnowStruct -> Repertoire -> Form -> Int -> State
             -> Maybe PlanTrace
extractTrace _ _ _ _ 0 _ = Just []  -- If the required horizon is 0, it returns an empty plan
extractTrace ags f rep goal j s = fmap (\v -> map (dec v) rounds) mwit
-- ^ If mwit= Nothing, return Nothing. If mwit= Just v, decode each saved round using the 
-- satisfying assignment v, producing Just trace
  where
    -- Rebuilding the unpruned path structure. This executes step for rounds 1 through j, starting with
    -- (f, lawOf f, [])
    (gk, zk, rounds) = foldl' step (f, lawOf f, []) [1 .. j]
    -- gk is the knowledge structure after j unpruned union rounds.z
    -- zk is the cumulative guard after those rounds. 
    -- rounds contains each round's choice bits and its per-branch allocated atoms.

    -- one unpruned round: apply the union, extend the guard, and remember
    -- this round's bits and branch atoms for decoding
    step :: (KnowStruct, Bdd, [([Prp], [[Prp]])]) -> Int -> (KnowStruct, Bdd, [([Prp], [[Prp]])])
    step (g, z, acc) r = (g', con z (con (mpPts u) lawB), acc ++ [(bits, brAts)])
      where
        (u, bits, brAts, _) = instantiateUnion ags rep r  -- meta not needed here
        -- ^ creates the round’s union event and gets: u: the constructed union MPEvent;
        -- bits: fresh choice-bit propositions for branch selection; brAts: the fresh 
        -- atom allocation for each repertoire branch; _: metadata
        (g', lawB) = applyEvent g u
        -- ^ extends the knowledge structure.

    -- Some designated, law-abiding run from s that reaches the goal, as a
    -- total assignment over the full vocabulary, so every bit and every
    -- branch atom has a value.
    mwit :: Maybe [(Int, Bool)]
    mwit = anySatWith (map unP (vocabOf gk))
        (conSet [zk, bddOf gk goal, cubeOf (vocabOf f) s])
        -- This asks for one total satisfying assignment over the whole final vocabulary 
        -- of gk satisfying: z_k /\ ||goal||_gk /\ cube_{V_0}(s)

    -- decode round r's part of the witness: which branch fired, and what
    -- its atoms got set to
    dec :: [(Int, Bool)] -> ([Prp], [[Prp]]) -> (String, [(String, Bool)])
    dec v (bits, brAts) =
        ( esName spec
        , [ (nm, fromMaybe False (lookup (unP q) v))
          | (nm, q) <- zip (esAtoms spec) qs   -- declared names <-> fresh atoms
          ]
        )
      where
        -- identify the branch
        i :: Int
        i = decodeBranch bits v  -- read the branch index off the choice bits

        -- select the repertoire branch i
        spec :: MPEventSchema
        spec = branchesOf rep !! (i - 1)  -- 1-indexed branch, 0-indexed list

        qs :: [Prp]
        qs = brAts !! (i - 1)  -- that branch's fresh atoms in this round

{- | Independently validates an extracted plan.

The plan is replayed as sequential single-pointed event update
 The goal is then evaluated using SMCDEL

Replay atoms for round @r@ use ids starting at @1000 * r + 500@, which
are disjoint from the atoms that are allocated by the search constructions.
-}
verifyTrace :: [Agent] -> Repertoire -> Form -> KnowStruct -> State
            -> PlanTrace -> Bool
verifyTrace _ags rep goal = go 1  -- round counter starts at 1, like the search
  where
    -- walk the plan, one single-pointed update per entry, then evaluate
    go :: Int -> KnowStruct -> State -> PlanTrace -> Bool
    go _ g s [] = evalViaBdd (g, sort s) goal  -- states are kept sorted
    go r g s ((nm, ev) : rest) =
        -- find the branch this plan entry names
        case lookup nm [ (esName b, b) | b <- branchesOf rep ] of
            Nothing -> False  -- an unknown action name: the plan is rejected
            Just b ->
                -- fresh atoms for the replay, block 1000r+500..; these can't
                -- collide with anything either search allocated
                let qs = [ P (1000 * r + 500 + j)
                         | j <- [0 .. length (esAtoms b) - 1]
                         ]
                    -- The fired event: the atoms the plan sets to true.
                    x = [ q | (q, (_, True)) <- zip qs ev ]
                    lawB = bddOf g (esLaw b qs)  -- translate here, at this g
                    -- observables: keep O_i, add whatever the action grants i
                    obs' = [ (i, obsFor g i ++ fromMaybe [] (lookup i (esObs b qs)))
                           | i <- agentsOf g
                           ]
                    -- F x X, same three pieces as applyEvent
                    g' = KnS (vocabOf g ++ qs) (con (lawOf g) lawB) obs'
                    s' = sort (s ++ x)  -- new state: old atoms plus the event
                    -- The new state must satisfy the translated law, and the
                    -- event must be designated, we only continue if this is the case
                    okSt = evaluateFun lawB (\n -> P n `elem` s')
                    okPt = evaluateFun (esPts b qs) (\n -> P n `elem` x)
                in okSt && okPt && go (r + 1) g' s' rest

-- * Printing

-- | Renders a plan as semicolon-separated action instances.
--
-- Each action is followed by the truth values of its event atoms:
-- @\"senseP x=1 ; tellQ x=0\"@.
showTrace :: PlanTrace -> String
showTrace [] = "(empty plan)"
showTrace tr = intercalate " ; "
    [ nm ++ concat [ " " ++ n ++ "=" ++ (if b then "1" else "0") | (n, b) <- ev ]
    | (nm, ev) <- tr
    ]

-- | Renders an outcome for a one-line summary.
verdictOf :: Outcome -> String
verdictOf (PlanFound k _) = "plan found at horizon " ++ show k
verdictOf (NoPlan k why)  = "no plan (" ++ why ++ ", round " ++ show k ++ ")"
verdictOf (Exhausted k)   = "undecided up to horizon " ++ show k


-- | Reports if all extracted plans passed the independent replay
verifiedOf :: Outcome -> String
verifiedOf (PlanFound _ ps)
    | and [ ok | (_, _, ok) <- ps ] = "replay PASS"
    | otherwise = "replay FAIL"
verifiedOf _ = ""

-- | Renders the result of one search configuration.
renderCell :: Bool -> SearchResult -> String
renderCell verbose sr = unlines (logLines ++ histLines ++ outLines)
  where
    logLines :: [String]
    logLines
        | verbose = map ("  " ++) (srLog sr)  -- indent under the banner
        | otherwise = []

    histLines :: [String]
    histLines
        | verbose =
            [ "  horizon " ++ show k ++ ": weakAll=" ++ show (weakAll r)
                ++ " strongAll=" ++ show (strongAll r)
                ++ " weakEx=" ++ show (weakEx r)
                ++ " strongEx=" ++ show (strongEx r)
            | (k, r) <- srHist sr
            ]
        | otherwise = []

    -- the results block, depending on how the search ended
    outLines :: [String]
    outLines = case srOutcome sr of
        PlanFound k ps ->
            ("  PLAN FOUND (horizon " ++ show k ++ ")")
            -- per initial state: the plan, and how the replay went
            : [ "    from " ++ show (map unP s) ++ ": "
                    ++ maybe "?" showTrace mtr
                    ++ "  [replay: " ++ (if ok then "PASS" else "FAIL") ++ "]"
              | (s, mtr, ok) <- ps
              ]
        NoPlan k why ->
            [ "  NO PLAN EXISTS (certified by " ++ why
                ++ " at round " ++ show k ++ ")"
            ]
        Exhausted k -> [ "  undecided up to horizon " ++ show k ]


-- * Running the benchmarks

-- | One benchmark instance: everything that is needed for a search variant
data Problem = Problem
    { prAgents :: ![Agent]
    , prStart  :: !KnowStruct  -- ^ the initial structure
    , prInit   :: ![State]     -- ^ the designated initial states
    , prRep    :: !Repertoire
    , prGoal   :: !Form
    }

-- | Dispatch: the tree has its own search, the other three share the
-- pipeline
runSearch :: Variant -> Int -> Problem -> SearchResult
runSearch VTree maxR pr =
    searchTree maxR (prAgents pr) (prStart pr) (prInit pr) (prRep pr) (prGoal pr)
runSearch v maxR pr =
    searchPipeline v maxR (prAgents pr) (prStart pr) (prInit pr) (prRep pr)
        (prGoal pr)

-- | One line of the summary table.
data Row = Row
    { rowName    :: !String
    , rowVariant :: !String
    , rowVerdict :: !String
    , rowSecs    :: !(Maybe Double)  -- ^ cpu seconds; Nothing on timeout
    , rowPeak    :: !(Maybe Int)     -- ^ the largest law BDD of the run
    , rowVocab   :: !(Maybe Int)     -- ^ the vocabulary at the last horizon
    , rowCheck   :: !String          -- ^ the replay verdict, when there is one
    } deriving stock (Show)

-- | "-" for a timeout, three decimals otherwise.
fmtSecs :: Maybe Double -> String
fmtSecs Nothing  = "-"
fmtSecs (Just s) = printf "%.3f" s  -- printf's result type comes from context

-- | Padding column width to the right; entries that are too long are left intact.
pad :: Int -> String -> String
pad n s = s ++ replicate (max 0 (n - length s)) ' '  -- max 0: never chop

-- | The summary table at the very end of a run
printTable :: [Row] -> IO ()
printTable rows = do
    putStrLn header
    mapM_ (putStrLn . line) rows
  where
    -- column widths here and in 'line' below have to match
    header :: String
    header = pad 10 "instance" ++ pad 53 "variant" ++ pad 44 "result"
        ++ pad 10 "cpu (s)" ++ pad 10 "peak law" ++ pad 10 "end vocab"
        ++ "check"

    line :: Row -> String
    line r = pad 10 (rowName r) ++ pad 53 (rowVariant r)
        ++ pad 44 (rowVerdict r)
        ++ pad 10 (fmtSecs (rowSecs r))
        ++ pad 10 (maybe "-" show (rowPeak r))
        ++ pad 10 (maybe "-" show (rowVocab r))
        ++ rowCheck r

-- keep in sync with csvLine below
csvHeader :: String
csvHeader = "instance,variant,result,cpu_seconds,peak_law_size,end_vocab,replay"

-- | One csv row. The variant and result strings contain commas themselves,
-- that's why we have the quoting.
csvLine :: Row -> String
csvLine r = intercalate ","
    [ rowName r
    , quoted (rowVariant r)
    , quoted (rowVerdict r)
    , fmtSecs (rowSecs r)
    , maybe "" show (rowPeak r)
    , maybe "" show (rowVocab r)
    , rowCheck r
    ]
  where
    quoted :: String -> String
    quoted str = "\"" ++ str ++ "\""   -- fine: nothing we write contains quotes

-- | Everything the command line can set.
data Options = Options
    { optMax      :: !Int    -- ^ horizon cap: give up after this
    , optTimeout  :: !Int             -- ^ wall-clock seconds per cell 
    , optVariants :: ![Variant]       -- ^ run exactly these; empty until named
    , optCsv      :: !(Maybe FilePath)   -- ^ also write the summary here, if set
    , optQuiet    :: !Bool            -- ^ suppress the logs and readings
    , optNames    :: ![String]   -- ^ the instances, in the given order
    } deriving stock (Show)

-- | What you get with no flags: horizon 10, a minute per cell, no csv,
-- verbose output.
defaultOptions :: Options
defaultOptions = Options
    { optMax      = 10
    , optTimeout  = 60
    , optVariants = []  -- none until named on the command line
    , optCsv      = Nothing
    , optQuiet    = False
    , optNames    = []
    }

-- | Flag parsing. A variant name selects that variant; every
-- other argument is taken for an instance name, in the given order.
parseArgs :: [String] -> Options
parseArgs = foldl' step defaultOptions   -- fold the args into the record
  where
    -- stripPrefix gives Just the rest exactly when the flag matches; read
    -- crashes on garbage numbers
    step :: Options -> String -> Options
    step o a
        | Just v <- stripPrefix "--max=" a = o { optMax = read v }
        | Just v <- stripPrefix "--timeout=" a = o { optTimeout = read v }
        | Just v <- stripPrefix "--variants=" a =
            o { optVariants = optVariants o ++ map toVariant (splitOn ',' v) }
            -- accumulate, don't replace: mixing the flag and bare names works
        | Just v <- stripPrefix "--csv=" a = o { optCsv = Just v }
        | a == "--quiet" = o { optQuiet = True }
        | Just v <- lookup a variantsByName =
            o { optVariants = optVariants o ++ [v] }  -- a bare variant name
        | otherwise = o { optNames = optNames o ++ [a] }  --else: an instance

    -- only reachable through --variants=...; bare names have already matched above
    toVariant :: String -> Variant
    toVariant s = fromMaybe
        (error ("unknown variant " ++ show s ++ "; use tree, union, prune, full"))
        (lookup s variantsByName)

-- | Splits a string wherever a chosen character occurs
splitOn :: Char -> String -> [String]
splitOn c s = case break (== c) s of
    (piece, [])       -> [piece]  -- no separator left: this was the last piece
    (piece, _ : rest) -> piece : splitOn c rest  -- drop the comma, keep going

-- | One cell of the table: run, force, time, print.
runCell :: Options -> String -> Problem -> Variant -> IO Row
-- opts: command-line settings such as horizon, timeout, and quiet mode.
-- nm: the instance name. pr: the problem instance. v: the selected search variant
runCell opts nm pr v = do
    putStrLn ("-- " ++ variantName v)
    res <- timeout (optTimeout opts * 1000000) $ do  -- microseconds
        t0 <- getCPUTime
        let sr = runSearch v (optMax opts) pr  -- nothing has run yet
        let detail = renderCell (not (optQuiet opts)) sr
        _ <- evaluate (length detail)  -- force the search behind the report
        t1 <- getCPUTime
        -- getCPUTime counts picoseconds
        let secs = fromIntegral (t1 - t0) / 1.0e12 :: Double
        pure (sr, detail, secs)
    case res of
        Nothing -> do  -- the timeout fired
            putStrLn ("  no answer within " ++ show (optTimeout opts) ++ "s")
            -- a mostly-empty row, so the table still lines up
            pure (Row nm (variantName v) "timeout" Nothing Nothing Nothing "")
        Just (sr, detail, secs) -> do
            putStr detail
            -- Non-empty by construction: horizon 0 is always recorded
            let (_, endVocab, _) = last (srSizes sr)
            pure Row
                { rowName    = nm
                , rowVariant = variantName v
                , rowVerdict = verdictOf (srOutcome sr)
                , rowSecs    = Just secs
                , rowPeak    = Just (srPeak sr)
                , rowVocab   = Just endVocab
                , rowCheck   = verifiedOf (srOutcome sr)
                }


-- | All requested variants on one instance, or a complaint if the name is
-- unknown.
runProblem :: Options -> String -> IO [Row]
runProblem opts nm = case lookupProblem nm of
    Nothing -> do
        putStrLn ("unknown instance " ++ show nm ++ "; known: " ++ knownNames)
        pure []
    Just pr -> do
        putStrLn ""
        putStrLn ("==== " ++ nm ++ " (horizon cap " ++ show (optMax opts)
            ++ ", timeout " ++ show (optTimeout opts) ++ "s) ====")
        mapM (runCell opts nm pr) (optVariants opts)

-- | Parse the flags, make sure that at least one variant is named, run every
-- requested cell, print the summary, and write the csv
main :: IO ()
main = do
    opts0 <- parseArgs <$> getArgs
    -- nub keeps the first occurrence, so the order you typed is the order run
    opts <- case nub (optVariants opts0) of
        [] -> die ("no variant named; pick at least one of "
            ++ intercalate ", " (map fst variantsByName)
            ++ ", for example: main peekA prune full")
        vs -> pure opts0 { optVariants = vs }  -- deduplicated, in given order
    -- no instance named: fall back to the demo set
    let names = if null (optNames opts) then defaultNames else optNames opts
    rows <- concat <$> mapM (runProblem opts) names  -- [[Row]], flattened
    putStrLn ""
    putStrLn "== summary =="
    printTable rows
    case optCsv opts of
        Nothing -> pure ()  -- no csv wanted
        Just fp -> do
            writeFile fp (unlines (csvHeader : map csvLine rows))
            putStrLn ("csv written to " ++ fp)


-- * Example Domains 

-- The story is the running example of the thesis (starting from Example 3.1)
-- Johan may or may not have decided to throw a surprise party for Malvin's
-- birthday, and Alice, Bob and Charlie are trying to find out. The detail
-- domains continue it as in sec:pr-audience. The peek shape is 
--  also in the letter of Gattinger 2018, Exs. 1.3.3 and 2.5.6, as mentioned in
-- Example 4.35

-- | Alice, Bob and Charlie, the three friends of the party 
partyAgents :: [Agent]
partyAgents = ["a", "b", "c"]

-- | Just Alice and Bob, we don't care about charlie here
abAgents :: [Agent]
abAgents = ["a", "b"]

-- | The party is on, and Johan has decided whether to throw it.
partyOn, isDecided :: Prp
partyOn   = P 0
isDecided = P 1

{- | The base of Example 3.1: the law rules out a party that is on
before Johan decided to throw it, and nobody observes anything. Three
states: undecided, decided against, and it is on.
-}
partyF :: KnowStruct
partyF = KnS [partyOn, isDecided]
    (imp (var (unP partyOn)) (var (unP isDecided)))  -- p -> d, as a BDD
    [ (i, []) | i <- partyAgents ]

-- | All three states, designated: we know nothing
partyStates :: [State]
partyStates = [[], [isDecided], [partyOn, isDecided]]

{- | "Learn whether p, seen by exactly these agents": one event atom x,
law x <-> p, both outcomes designated. We use this shape multiple times
below
-}
learnWhether :: String -> [Agent] -> Prp -> MPEventSchema
learnWhether nm who p = MPEventSchema
    { esName  = nm
    , esAtoms = ["x"]
    , esLaw   = \qs -> Equi (PrpF (head qs)) (PrpF p)  -- x <-> p
    , esObs   = \qs -> [ (i, [head qs]) | i <- who ]
    , esPts   = const top  -- both outcomes designated: the sensing part
    }

{- | Example 5.33 Alice sneaks a look at Johan's planner.The copy records
whether the party is on, only she sees it, and the others just see that she
looked, via the public choice bit. Repeating the peek does not give anything new, 
and the prune variant reports that as a literal fixpoint after one round.
-}
peekRep :: Repertoire
peekRep = Repertoire [learnWhether "peek" ["a"] partyOn]

-- | The calendar is lieing somewhere unattended: in one branch Alice sneaks the
-- look, in the other Bob does.
shareRep :: Repertoire
shareRep = Repertoire
    [ learnWhether "peekA" ["a"] partyOn
    , learnWhether "peekB" ["b"] partyOn
    ]


{- | Alice peeks, and can then tell this to Bob: the reveal's atom records
whether K_a p holds, and Bob sees it. After a peek Alice knows whether p,
so hearing that she does not know p tells Bob that p is false, and Bob knows
whether the party is on, from every state. We do not care about Charlie, still. 
The modal law is retranslated against the current structure at whatever round
it fires; this is why 'esLaw' returns a Form and not a Bdd.
-}
relayRep :: Repertoire
relayRep = Repertoire
    [ learnWhether "peek" ["a"] partyOn
    , MPEventSchema
        { esName  = "reveal"
        , esAtoms = ["r"]
        , esLaw   = \qs -> Equi (PrpF (head qs)) (K "a" (PrpF partyOn))
        , esObs   = \qs -> [("a", [head qs]), ("b", [head qs])]
        , esPts   = const top
        }
    ]


--  It is settled that there will be a party, we now show off the methods of Section A.6

-- | The open details:  will the party be at Johan's place, 
-- cake, music.
atJohans, cake, music :: Prp
atJohans = P 0
cake     = P 1
music    = P 2

-- | The base of Example A.10: two independent
-- details, law top, nobody informed. Charlie has gone home.
detailsF :: KnowStruct
detailsF = KnS [atJohans, cake] top [("a", []), ("b", [])]

-- | The same with a third detail, for the arity-3 question
detailsF3 :: KnowStruct
detailsF3 = KnS [atJohans, cake, music] top [("a", []), ("b", [])]

{- | The two private questions of Section A.6 in branch i Alice asks
Johan about detail i, the answer lands on the event atom, and Bob only
sees that a question was asked. Full-Psi pruning removes nothing,
since along some path each copy is Alice's only access to its detail. 
THIS IS THE whole motivation for the audience scan.
-}
askRep :: Repertoire
askRep = Repertoire
    [ learnWhether "askPlace" ["a"] atJohans
    , learnWhether "askCake"  ["a"] cake
    ]

{- | askRep plus a text: Alice forwards the cake answer to Bob, but not
the place. With the goal that Bob learns the place, the audience is just Bob, 
so the vocabulary grows without bound and no two stages are ever literally equal. 
Stages 1 and 0 are not linked,
stages 2 and 1 are, so the full variant certifies at its second attempt.
This is Example A.16
-}
tellRep :: Repertoire
tellRep = Repertoire
    [ learnWhether "askPlace" ["a"] atJohans
    , learnWhether "askCake"  ["a"] cake
    , learnWhether "textCake" ["a", "b"] cake  -- the only branch Bob hears
    ]

{- | One compound question: Alice corners Johan and asks about all three
details at once. One branch, three event atoms, so branches of arity above
one are used too.
-}
askAllRep :: Repertoire
askAllRep = Repertoire
    [ MPEventSchema
        { esName  = "askAll"
        , esAtoms = ["x0", "x1", "x2"]
        , esLaw   = \qs -> Conj
            (zipWith (\q p -> Equi (PrpF q) (PrpF p)) qs [atJohans, cake, music])
            -- copies paired with details: x0 <-> place, x1 <-> cake, and so on
        , esObs   = \qs -> [("a", qs)]  -- Alice hears all three answers
        , esPts   = const top
        }
    ]


-- The Muddy Children puzzle can be viewed as an epistemic planning problem 
-- because the parent's public announcements are actions that change the children's 
-- knowledge. The goal is for every muddy child to eventually know that they are muddy; 
-- the plan is a sequence of truthful public announcements or queries designed to
-- make that knowledge condition hold.

-- | Child i's mud atom: child \"1\" owns @P 0@, child \"2\" owns @P 1@, and
-- so on.
mAt :: Agent -> Prp
mAt i = P (read i - 1)

-- | Every child sees the other children's foreheads and not its own; the
-- law is top, so all combinations are states.
muddyF :: [Agent] -> KnowStruct
muddyF kids = KnS [ mAt i | i <- kids ] top
    [ (i, [ mAt j | j <- kids, j /= i ]) | i <- kids ]
    -- child i observes everyone's atom but its own

{- | Two public announcements, hence arity 0: no event atoms, no added
observables.
The law of silence is modal and is translated against the current structure
each time it is applied. Knowing whether is 'Kw'. The union of the two
branches carries one public choice bit per round, so which announcement
happened is common knowledge (which makes sense).
-}
muddyRep :: [Agent] -> Repertoire
muddyRep kids = Repertoire
    [ MPEventSchema
        { esName  = "father"
        , esAtoms = []
        , esLaw   = const (Disj [ PrpF (mAt i) | i <- kids ])  -- someone is muddy
        , esObs   = const []
        , esPts   = const top
        }
    , MPEventSchema
        { esName  = "silence"
        , esAtoms = []
        , esLaw   = const (Conj [ Neg (Kw i (PrpF (mAt i))) | i <- kids ])
          -- "no child knows whether it is muddy yet"
        , esObs   = const []
        , esPts   = const top
        }
    ]

-- | Every child knows whether it is muddy.
muddyGoal :: [Agent] -> Form
muddyGoal kids = Conj [ Kw i (PrpF (mAt i)) | i <- kids ]


-- * Instances and scaling

-- | The muddy children with all children muddy initially.
muddyProblem :: Int -> Problem
muddyProblem n = Problem
    { prAgents = kids
    , prStart  = muddyF kids
    , prInit   = [[ mAt i | i <- kids ]]
    , prRep    = muddyRep kids
    , prGoal   = muddyGoal kids
    }
  where
    kids :: [Agent]
    kids = map show [1 .. n]


{- | n independent details, one private question per detail, all answered
to Alice. the askN family generalises the audience example. The plan needs
one round per detail, so the tree grows like n^d while the union adds jsut
some atoms per round
-}
askProblem :: Int -> Problem
askProblem n = Problem
    { prAgents = abAgents
    , prStart  = KnS [ P i | i <- [0 .. n - 1] ] top [("a", []), ("b", [])]
    , prInit   = [[ P i | i <- [0 .. n - 1] ]]  -- every detail happens to hold
    , prRep    = Repertoire
        [ learnWhether ("ask" ++ show i) ["a"] (P i) | i <- [0 .. n - 1] ]
    , prGoal   = Conj [ K "a" (PrpF (P i)) | i <- [0 .. n - 1] ]  -- knows all
    }

-- | The same repertoire with the goal that Bob learns the first detail: no
-- action informs him, so this is certifiably impossible, and the
-- family makes the cost of the certificates clear 
askBProblem :: Int -> Problem
askBProblem n = (askProblem n) { prGoal = K "b" (PrpF (P 0)) }

{- | The named instances. 
-}
namedProblems :: [(String, Problem)]
namedProblems =
    [ ("peekA", Problem partyAgents partyF partyStates peekRep
          (Kw "a" (PrpF partyOn)))
    , ("peekB", Problem partyAgents partyF partyStates peekRep
          (Kw "b" (PrpF partyOn)))
      -- no plan: only Alice ever sees a copy; Example 5.33's fixpoint, round 1
    , ("share", Problem partyAgents partyF partyStates shareRep
          (Kw "a" (PrpF partyOn)))
      -- weak but not strong: Bob's branch doesnt help A
    , ("relay", Problem partyAgents partyF partyStates relayRep
          (Kw "b" (PrpF partyOn)))
      -- peek, then reveal: the plan needs the modal law
    , ("askA", Problem abAgents detailsF (subsequences [atJohans, cake]) askRep
          (Conj [Kw "a" (PrpF atJohans), Kw "a" (PrpF cake)]))
    , ("askB", Problem abAgents detailsF (subsequences [atJohans, cake]) askRep
          (Kw "b" (PrpF atJohans)))
      -- the blow-up of A.6: prune keeps everything, full collapses
    , ("tell", Problem abAgents detailsF (subsequences [atJohans, cake]) tellRep
          (Kw "b" (PrpF atJohans)))
      -- Example A.16: only the link certificate can do anything cool
    , ("askAll", Problem abAgents detailsF3
          (subsequences [atJohans, cake, music]) askAllRep
          (Kw "b" (PrpF atJohans)))  -- no plan either
    ]

-- | Named instances first, then the prefix-plus-number families.
lookupProblem :: String -> Maybe Problem
lookupProblem nm
    | Just p <- lookup nm namedProblems = Just p
    | Just k <- family "muddy" = Just (muddyProblem k)
    | Just k <- family "askb" = Just (askBProblem k)  -- before the ask case
    | Just k <- family "ask" = Just (askProblem k)
    | otherwise = Nothing
  where
    -- does nm look like pre<digits>? then read out the number
    family :: String -> Maybe Int
    family pre = case stripPrefix pre nm of
        Just ds | not (null ds), all isDigit ds -> Just (read ds)  -- read is safe
        _ -> Nothing

-- | The demo set that runs when the input does not name an instance.
defaultNames :: [String]
defaultNames = ["peekA", "peekB", "askA", "askB", "tell", "muddy3", "relay"]

-- | For the "unknown instance" complaint in 'runProblem'
knownNames :: String
knownNames = intercalate ", " (map fst namedProblems)
    ++ ", and the families muddyN, askN, askbN"