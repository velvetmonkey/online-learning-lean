# online-learning-lean

[![Lean 4](https://img.shields.io/badge/Lean-4.28.0-blue)](https://lean-lang.org/)
[![Mathlib](https://img.shields.io/badge/Mathlib-v4.28.0-purple)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg)](LICENSE)
[![Proofs](https://img.shields.io/badge/proofs-proven%20%2F%200%20sorry-brightgreen)](OnlineLearning)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.20480528.svg)](https://doi.org/10.5281/zenodo.20480528)

**online-learning-lean: Formal Proofs of FTRL Regret Bounds in Lean 4**

Lean 4 formal proofs for Follow-the-Regularised-Leader (FTRL) in online convex optimisation. The development covers subgradient regret, Bregman divergence regularisation, per-step stability and approximation estimates, the Bregman regret bound, and an O(sqrt(K)) regret rate.

**Zero sorry statements.** Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).

## Why it matters

Online convex optimisation studies repeated decision-making under adversarially chosen convex losses. At each round, the learner chooses a point in a convex constraint set, observes a loss, and is measured by regret against a fixed comparator.

Follow-the-Regularised-Leader is a central online learning algorithm. It balances cumulative linearised loss against a strongly convex regulariser. With a Bregman divergence regulariser and bounded subgradients, the standard analysis proves O(sqrt(K)) regret after `K` rounds.

This library machine-checks the Bregman-divergence proof of that regret bound in Lean 4.

## Setting

A general real inner product space `E`, a constraint set `C`, iterates `x : Nat -> E`, subgradients `g : Nat -> E`, learning rate `eta`, regulariser `phi`, and regulariser gradient `gradphi`.

The linearised regret against a comparator `u` is:

```text
regret(u) = sum_{k<K} <g_k, x_k - u>
```

The Bregman divergence is:

```text
D_phi(x, y) = phi(x) - phi(y) - <gradphi(y), x - y>
```

The FTRL update is represented by its first-order optimality condition:

```text
0 <= <eta * g_k + gradphi(x_{k+1}) - gradphi(x_k), y - x_{k+1}>
```

for every feasible `y`. The regulariser is assumed 1-strongly convex through:

```text
||a - b||^2 / 2 <= D_phi(a, b)
```

## Main result

With bounded subgradients `||g_k|| <= G`, comparator divergence bounded by `D0`, positive `G`, `D0`, and `K`, and optimal learning rate:

```text
eta = sqrt(2 * D0 / (K * G^2))
```

the final theorem proves:

```text
regret(u) <= G * sqrt(2 * D0 * K)
```

This is the standard O(sqrt(K)) FTRL regret bound.

## Project structure

```text
OnlineLearning/
├── Defs.lean        — IsSubgradientAt, bregmanDiv, FTRLSetup,
│                      ftrl_step, regret
├── Stability.lean   — Bregman identities, regret decomposition,
│                      per-step FTRL stability
└── Convergence.lean — approximation bound, combined per-step bound,
                       Bregman regret bound, bounded-gradient regret bound,
                       O(sqrt(K)) convergence theorem
OnlineLearning.lean  — Root module
```

## Theorem inventory

| # | Name | Statement |
|---|------|-----------|
| 1 | `bregmanDiv_self` | `D_phi(x, x) = 0` |
| 2 | `FTRLSetup.bregman_nonneg` | Under strong convexity, `0 <= D_phi(a, b)` |
| 3 | `bregman_three_point` | `D_phi(a,c) = D_phi(a,b) + D_phi(b,c) + <gradphi(b)-gradphi(c), a-b>` |
| 4 | `inner_sub_split` | `<g, x-u> = <g, x-y> + <g, y-u>` |
| 5 | `regret_decomposition` | Regret splits into stability terms plus approximation terms |
| 6 | `ftrl_stability` | `eta <g_k, x_k-x_{k+1}> - D_phi(x_{k+1},x_k) <= eta^2 ||g_k||^2 / 2` |
| 7 | `approximation_bound` | `eta <g_k, x_{k+1}-u> <= D_phi(u,x_k) - D_phi(u,x_{k+1}) - D_phi(x_{k+1},x_k)` |
| 8 | `combined_per_step` | `eta <g_k, x_k-u> <= D_phi(u,x_k) - D_phi(u,x_{k+1}) + eta^2 ||g_k||^2 / 2` |
| 9 | `scaled_regret_bound` | `eta * regret(u) <= D_phi(u,x_0) + eta^2/2 * sum_{k<K} ||g_k||^2` |
| 10 | `bregman_regret_bound` | `regret(u) <= D_phi(u,x_0)/eta + eta/2 * sum_{k<K} ||g_k||^2` |
| 11 | `ftrl_regret_bound` | If `||g_k|| <= G`, then `regret(u) <= D_phi(u,x_0)/eta + eta * K * G^2 / 2` |
| 12 | `ftrl_convergence` | With optimal `eta`, `regret(u) <= G * sqrt(2 * D0 * K)` |

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [mirror-descent-lean](https://github.com/velvetmonkey/mirror-descent-lean) — Lean 4 mirror descent with Bregman divergences
- [sgd-lean](https://github.com/velvetmonkey/sgd-lean) — Lean 4 bounded-noise SGD convergence
- [subgradient-lean](https://github.com/velvetmonkey/subgradient-lean) — Lean 4 subgradient method convergence
- [frank-wolfe-lean](https://github.com/velvetmonkey/frank-wolfe-lean) — Lean 4 Frank-Wolfe convergence

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline — zero sorry, standard axioms only — was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
