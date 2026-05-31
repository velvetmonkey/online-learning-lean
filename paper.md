# online-learning-lean: Formal Proofs of FTRL Regret Bounds in Lean 4

Ben Cassie  
ORCID: 0009-0004-1899-7627  
2026-05-31

## Abstract

`online-learning-lean` is a Lean 4 / Mathlib library formalising Follow-the-Regularised-Leader for online convex optimisation in a real inner product space. The development defines subgradient conditions, Bregman divergence, the FTRL setup, linearised regret, per-step stability and approximation bounds, a Bregman regret theorem, and the standard `O(sqrt K)` regret rate for bounded subgradients. The proof method is the classical Bregman three-point identity plus telescoping. The formal development is machine-checked in Lean 4 with zero `sorry`, zero `admit`, and standard Lean/Mathlib axioms only.

## 1. Introduction

Online convex optimisation models repeated decisions against a sequence of convex losses. At round `k`, the learner plays `x_k`, observes a subgradient `g_k`, and is evaluated by regret against a fixed comparator `u`. Follow-the-Regularised-Leader stabilises this process by balancing cumulative linearised loss with a strongly convex regulariser.

The repository formalises the deterministic core of that analysis. It does not model an adversary or probability distribution. Instead, it assumes a finite horizon `K`, a feasible set, iterates, subgradients, a Bregman regulariser, and the first-order optimality condition for each FTRL step. This is enough to prove the regret guarantee that is normally used as the algebraic backbone of FTRL analyses.

## 2. Mathematical Setting

The type `E` is a real inner product space. `OnlineLearning/Defs.lean` defines

```text
IsSubgradientAt f g x :=
  forall y, f y >= f x + <g, y - x>
```

and the Bregman divergence

```text
D_phi(x, y) = phi x - phi y - <gradphi y, x - y>.
```

An `FTRLSetup` packages the feasible set `C`, iterates `x`, subgradients `g`, horizon `K`, learning rate `eta`, regulariser `phi`, gradient `gradphi`, feasibility hypotheses, strong convexity as a Bregman lower bound, and the FTRL optimality condition. Regret against `u` is

```text
sum_{k<K} <g_k, x_k - u>.
```

## 3. Main Theorems

`Stability.lean` proves `bregmanDiv_self`, `FTRLSetup.bregman_nonneg`, and `bregman_three_point`. It then proves `regret_decomposition`, splitting regret into stability terms and approximation terms, and `ftrl_stability`:

```text
eta * <g_k, x_k - x_{k+1}> - D_phi(x_{k+1}, x_k)
  <= eta^2 * ||g_k||^2 / 2.
```

`Convergence.lean` proves `approximation_bound` and combines it with stability in `combined_per_step`:

```text
eta * <g_k, x_k - u>
  <= D_phi(u, x_k) - D_phi(u, x_{k+1})
     + eta^2 * ||g_k||^2 / 2.
```

After summing, `bregman_regret_bound` gives

```text
regret(u) <= D_phi(u, x_0) / eta
             + eta / 2 * sum_{k<K} ||g_k||^2.
```

With `||g_k|| <= G`, `ftrl_regret_bound` gives the bounded-gradient version, and `ftrl_convergence` proves the optimized rate

```text
regret(u) <= G * sqrt(2 * D0 * K).
```

## 4. Proof Sketch

The proof is the standard Bregman telescoping proof. The three-point identity rewrites differences of Bregman divergences so that the FTRL optimality condition can control the approximation term. Young's inequality and the strong convexity lower bound control the stability term arising from moving from `x_k` to `x_{k+1}`.

The combined per-step theorem has the exact telescoping shape: `D_phi(u, x_k) - D_phi(u, x_{k+1})` appears on the right. Summing over `k < K` cancels all intermediate divergences and leaves only the initial comparator divergence plus a sum of squared subgradient norms. The final theorem substitutes the learning rate `eta = sqrt(2 * D0 / (K * G^2))` to obtain the `O(sqrt K)` bound.

## 5. Relation to Sibling Libraries

`online-learning-lean` is closest to `mirror-descent-lean`, DOI `10.5281/zenodo.20475033`, because both use Bregman divergences and a three-point identity. `sgd-lean`, DOI `10.5281/zenodo.20475583`, studies bounded-noise first-order optimisation, while `subgradient-lean`, DOI `10.5281/zenodo.20475946`, treats nonsmooth deterministic optimisation. `frank-wolfe-lean`, DOI `10.5281/zenodo.20478157`, is another first-order method whose proof also reduces to a one-step inequality and a global rate.

## 6. Conclusion

`online-learning-lean` gives a small, importable Lean 4 proof of the FTRL regret theorem under explicit Bregman and bounded-subgradient hypotheses. Future work could instantiate the abstract regulariser with entropy or Euclidean squared norm, connect the subgradient interface to concrete convex losses, and develop executable online-learning examples on finite decision sets.

## References

Shalev-Shwartz, S. (2012). *Online Learning and Online Convex Optimization*. Foundations and Trends in Machine Learning, 4(2), 107-194.

Hazan, E. (2016). *Introduction to Online Convex Optimization*. Foundations and Trends in Optimization, 2(3-4), 157-325.

The Mathlib Community. (2024). *The Lean Mathematical Library*. GitHub repository. <https://github.com/leanprover-community/mathlib4>

Cassie, B. (2026). *mirror-descent-lean: Formal Proofs of Mirror Descent and Bregman Divergence Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475033>

Cassie, B. (2026). *sgd-lean: Formal Proofs of Bounded-Noise SGD Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20475583>

Cassie, B. (2026). *frank-wolfe-lean: Formal Proofs of Frank-Wolfe Convergence in Lean 4*. Zenodo. <https://doi.org/10.5281/zenodo.20478157>
