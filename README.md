# epistemic-planner

A symbolic epistemic planner for [Dynamic Epistemic Logic](https://plato.stanford.edu/entries/dynamic-epistemic), built on the model checker [SMCDEL](https://github.com/jrclogic/SMCDEL).

Given a knowledge structure, a finite repertoire of epistemic actions, and a goal formula, the program searches for seauences of actions after which the goal holds. Where no such sequence exists it tries to certify this, instead of giving up at some depth. Every plan that is found is re-executed along an independent single-pointed code path and checked with SMCDEL. The verdict of the replay is printed next to the plan.

## Basic usage

1) Use *stack* from https://www.stackage.org

- `stack build` will build an executable `epistemic-planner`, and `stack install` copies it into `~/.local/bin`.

2) Pick an instance and at least one search variant. Run `stack run epistemic-planner -- peekA prune --max=3` resulting in:

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
    The round lines report the vocabulary and law size before the scan, then what the scan removed. The horizon lines give all four readings of the current stage: worlds universally or existentially, events by box or by diamond. The success criterion is the accumulated weak reading, so on instances with several initial states the per-horizon `weakAll` flag can read `False` on every line of a successful run. A certified impossibility looks like this instead:

```
    NO PLAN EXISTS (certified by link certificate at round 1)
```

3) The general form is

```
    stack run epistemic-planner -- [INSTANCE ...] [VARIANT ...] [OPTION ...]
```

    Instances, variants and options themselves can be mixed in any order and run in the given order. At least one variant must be named, either as a bare word or via `--variants=`. 


## Instances

All instances continue the running example of the thesis: Johan may or may not have decided to throw a surprise party, and Alice, Bob and Charlie would like to find out.

| name     | story                                                                               | verdict |
|----------|-------------------------------------------------------------------------------------|---------|
| `peekA`  | Alice peeks at the planner; does she learn whether the party is on?                 | plan at horizon 1 |
| `peekB`  | the same repertoire, but the goal is about Bob, who never sees a copy               | no plan; `prune` stops at the literal fixpoint |
| `share`  | Alice or Bob peeks; the goal is about Alice                                         | plan at horizon 1, weak but not strong |
| `relay`  | a peek, then a reveal whose event law is modal                                      | plan at horizon 2 |
| `askA`   | two private questions from Alice; she should learn both details                     | plan at horizon 2 |
| `askB`   | the same questions, but the goal is about Bob                                       | no plan; audience pruning stops at round 0 |
| `tell`   | `askB` plus a text that forwards only the answer to one of the questions to Bob     | no plan; only the link certificate stops |
| `askAll` | one compound question of arity 3, goal about Bob                                    | no plan; later copies are law-forced duplicates, so `prune` already stops |

The scaled families are `muddyN` (the muddy children as a planning problem, with all `N` children muddy; the plan is the father's announcement followed by rounds of silence), `askN` (one private question per detail, plan at horizon `N`) and `askbN` (the same repertoire with a goal about Bob, certifiably impossible). So `muddy4` or `ask3` are also valid instance names.

## Search variants

The same question is decided in four ways, so that run times, sizes and certificates can be compared on identical inputs.

- `tree` is the naive view: one structure and one guard per action sequence, so `m^d` structures at depth `d`. It can find plans and it can run out of horizon, but it can never certify impossibility.

- `union` is the composed view of Chapter 3: one structure per horizon, built by the public-choice union, without pruning. The vocabulary grows with every round, so a literal fixpoint can never appear.

- `prune` adds the full Psi scan of Chapter 5 after every round and uses the literal fixpoint as a convergence certificate.

- `full` prunes relative to the audience of the goal and the event laws, and additionally searches for the bisimulation link certificate of Appendix A, with the agreement precheck and the geometric schedule.

## Options

- `--max=K` sets the horizon cap; the search gives up after `K` rounds (default 10).
- `--timeout=S` sets a wall-clock limit in seconds per instance-and-variant cell (default 60). The `cpu (s)` column of the summary reports CPU time.
- `--variants=v1,v2` selects variants by a comma-separated list. These are appended to any variants named as bare words, and duplicates are dropped.
- `--csv=FILE` additionally writes the summary table to `FILE`.
- `--quiet` suppresses the round-by-round log and the per-horizon reading lines. Results, plans, replay verdicts and the summary table are still printed.


## References

Main reference for the constructions implemented here, also containing the
benchmark table:

- The accompanying thesis: the public-choice union is Chapter 3, the pruning pipeline and the literal fixpoint are Chapter 5, audience pruning and the link certificate are Appendix A.

Additional references:

- [Malvin Gattinger: *New Directions in Model Checking Dynamic Epistemic Logic.* PhD thesis, ILLC, Amsterdam, 2018](https://malv.in/phdthesis/).

- [Hans van Ditmarsch, Wiebe van der Hoek and Barteld Kooi: *Dynamic Epistemic Logic.* Synthese Library 337, Springer, 2008](https://doi.org/10.1007/978-1-4020-5839-4).

- [Thomas Bolander and Mikkel Birkegaard Andersen: *Epistemic planning for single- and multi-agent systems.* Journal of Applied Non-Classical Logics 21 (1), 2011](https://doi.org/10.3166/jancl.21.9-34).
