# epistemic-planner

A symbolic epistemic planning tool for [Dynamic Epistemic Logic](https://plato.stanford.edu/entries/dynamic-epistemic), built on [SMCDEL](https://github.com/jrclogic/SMCDEL).

Given a knowledge structure, a finite repertoire of epistemic actions, and a goal formula, this tool searches for action sequences after which the goal formula holds. If it cannot find such a sequence the tool tries to certify this. If a plan is found, the tool re-executes it along an independent single-pointed path. It then uses SMCDEL to check if the goal formula holds. The result of this replay is printed next to the found plan.

## Basic usage

1) Use *stack* (https://www.stackage.org)

- `stack build` builds an executable `epistemic-planner` instance, `stack install` copies this instance to `~/.local/bin`.

2) Choose at least one example and at least one search mode. For example, you could run `stack run epistemic-planner -- peekA prune --max=3`, which results in:

```
    ==== peekA (horizon cap 3, timeout 60s) ====
    -- prune: union + pruning (full Psi, literal fixpoint)
      round 1: vocab 4, law size 6
        pruned c1@1
      horizon 0: weakAll=False strongAll=False weakEx=False strongEx=False
      horizon 1: weakAll=True strongAll=True weakEx=True strongEx=True
      PLAN FOUND (horizon 1)
        from []: peek x=0  [replay: PASS]
        from [1]: peek x=0  [replay: PASS]
        from [0,1]: peek x=1  [replay: PASS]
```
The lines starting with `round` give the size of vocabulary and of the law before a pruning scan starts. The next line then shows what the scan has removed. The lines starting with `horizon` print the results of evaluating the four readings at the current stage, with the worlds read universally or existentially, and the events read by box or by diamond. The success criterion in this tool is given in the accumulated weak reading, this means that if instances have several initial states the per-horizon flag `weakAll` can be `False` on every line, but the run is still successful. If the tool finds a certificate for impossibility, it will instead print:

```
    NO PLAN EXISTS (certified by link certificate at round 1)
```

3) The general form of an input to the tool is

```
    stack run epistemic-planner -- [EXAMPLE ...] [VARIANT ...] [OPTION ...]
```
   where the examples, variants and options themselves can be given in any order and will then run in the given order. At least one variant must be given to the tool, either as a bare word (tree, union, prune, or full) or using the option `--variants=`. 


## Examples

All the examples given in the following table continue the running example of the thesis: Johan may or may not have decided to throw a surprise party; Alice, Bob and Charlie want to find out.

| name     | story                                                                               | verdict |
|----------|-------------------------------------------------------------------------------------|---------|
| `peekA`  | Alice looks at the planner, the goal is about Alice's knowledge afterwards          | plan found at horizon 1 |
| `peekB`  | Same as `peekA`, but with a goal about Bob's knowledge                              | no plan was found; `prune` stops at the literal fixpoint |
| `share`  | Alice or Bob peeks, the goal is about Alice's knowledge                             | plan found at horizon 1 |
| `relay`  | A peek; A reveal action has a modal event law                                       | plan found at horizon 2 |
| `askA`   | Alice asks two private questions, the goal is about her knowledge afterwards        | plan found at horizon 2 |
| `askB`   | Same as `askA` but with a goal about Bob's knowledge                                | no plan was found; audience pruning stops the search at round 0 |
| `tell`   | `askB`; a text that forwards the answer to one of the questions to Bob              | no plan was found; the link certificate stops the search |
| `askAll` | A question about three details, the goal is about Bob's knowledge                   | no plan was found; `prune` stops the search |

Additionally, there are the following scaled families of examples: `muddyN` (the Muddy Children Puzzle as a planning problem; here, all `N` children are muddy initially; the plan is the announcement of the father followed by rounds of silence), `askN` (Alice asks one private question for each of the `N` party details, the goal is about her knowledge afterwards; a plan can be found at horizon `N`), and `askbN` (same as `askN` but with a goal about Bob's knowledge; no plan can be found, but a certificate of impossibility is given). Names like `muddy4` or `ask3` can therefore also be used as input.

## Variants

The same input problem can be solved using four different search variants (`modes`). We use this to compare their run times, sizes and certificates on identical inputs.

- `tree`, corresponds to the naïve approach. The search tree is branched over the action sequences: one structure and guards per structure are generated for each action sequence. At depth `d`, this results in `m^d` structures. A plan can be found or reported not found for the given horizon, but this mode cannot be used to prove that no plan exists.

- `union` constructs one structure per horizon. It does not prune atoms. Since the vocabulary increases with every round, `union` cannot be used to detect a literal fixpoint.

- `prune` uses the composed public-choice construction that is used in `union` and pruning. This mode executes the full Psi scan of Chapter 5 after every round. It can detect literal fixpoints and prove that no further application of any action can affect the evaluation of the goal formula.

- `full` uses the composed public-choice construction and prunes relativized to the agents that are mentioned in the goal formula and the event laws. This mode also searches for a bisimulation link using the geometric schedule of Appendix A, after performing the agreement precheck described there.

## Options

Using the following options, we can change some of the default values that the tool assumes. 

- `--max=K` sets the horizon up to which the tool searches for a plan to `K`. The default is `K`=10.

- `--timeout=S` sets a time limit of `S` seconds for each search (that is, for each pair of example and search variant). The default is 60.
  
- `--variants=v1,v2` adds the search variants `v1` and `v2` to the search. Variants that are mentioned multiple times are ignored.
  
- `--csv=FILE` saves the results of the run to `FILE`. 
  
- `--quiet` hides the details of the search.

## References

The constructions that the implementations of this tool are based on, as well as the theory and proofs behind them, are developed in the MSc Logic thesis of Louise Wilk. The thesis summarises the benchmarks of the tool.

Additional references:

- [Malvin Gattinger: *New Directions in Model Checking Dynamic Epistemic Logic.* PhD thesis, ILLC, Amsterdam, 2018](https://malv.in/phdthesis/).

- [Hans van Ditmarsch, Wiebe van der Hoek and Barteld Kooi: *Dynamic Epistemic Logic.* Synthese Library 337, Springer, 2008](https://doi.org/10.1007/978-1-4020-5839-4).

- [Thomas Bolander and Mikkel Birkegaard Andersen: *Epistemic planning for single- and multi-agent systems.* Journal of Applied Non-Classical Logics 21 (1), 2011](https://doi.org/10.3166/jancl.21.9-34).
