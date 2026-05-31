import Mathlib

/-!
# Online Learning: Definitions

Follow-the-Regularised-Leader (FTRL) setup for online convex optimisation.

## Setting

Online convex optimisation over a convex set `C ⊆ E`.  At each round `k`,
the learner picks `x_k ∈ C`, an adversary reveals a convex loss, and the
learner suffers loss `f_k(x_k)`.  Regret against a comparator `u ∈ C`:

  `R_K = Σ_{k<K} f_k(x_k) − min_{x ∈ C} Σ_{k<K} f_k(x)`

We work with the linearised (subgradient) regret `Σ ⟨g_k, x_k − u⟩`.

## Main definitions

* `IsSubgradientAt` — subgradient oracle
* `bregmanDiv` — Bregman divergence `D_φ(x, y)`
* `FTRLSetup` — full FTRL configuration (iterates, subgradients, regulariser)
* `FTRLSetup.ftrl_step` — the FTRL update rule
* `FTRLSetup.regret` — linearised regret against a comparator
-/

noncomputable section

open Finset
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- ============================================================================
-- Subgradient oracle
-- ============================================================================

/-- `g` is a subgradient of `f` at `x` when `f(x) + ⟨g, y − x⟩ ≤ f(y)` for every `y`. -/
def IsSubgradientAt (f : E → ℝ) (g : E) (x : E) : Prop :=
  ∀ y, f x + ⟪g, y - x⟫_ℝ ≤ f y

-- ============================================================================
-- Bregman divergence
-- ============================================================================

/-- Bregman divergence associated to `(φ, ∇φ)`:
    `D_φ(x, y) = φ(x) − φ(y) − ⟨∇φ(y), x − y⟩`. -/
def bregmanDiv (φ : E → ℝ) (gradφ : E → E) (x y : E) : ℝ :=
  φ x - φ y - ⟪gradφ y, x - y⟫_ℝ

-- ============================================================================
-- FTRL setup
-- ============================================================================

/-- FTRL setup for online convex optimisation.

The learner plays iterates `x 0, x 1, …` in a constraint set `C`, and
observes subgradients `g 0, g 1, …` of convex losses.  The regulariser `φ`
with gradient oracle `gradφ` is **1-strongly convex** w.r.t. the ambient norm.

The FTRL update is characterised by the first-order optimality condition
(mirror-descent form):
  `∀ y ∈ C, ⟨η g_k + ∇φ(x_{k+1}) − ∇φ(x_k), y − x_{k+1}⟩ ≥ 0`

which defines
  `x_{k+1} = argmin_{x ∈ C} (η Σ_{i≤k} ⟨g_i, x⟩ + φ(x))`. -/
structure FTRLSetup (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  /-- Number of rounds. -/
  K : ℕ
  /-- Learning rate (step size), positive. -/
  η : ℝ
  /-- Convex constraint set. -/
  C : Set E
  /-- Regulariser (1-strongly convex). -/
  φ : E → ℝ
  /-- Gradient of the regulariser. -/
  gradφ : E → E
  /-- Iterates: `x 0` is the initial point, `x k` the iterate used at round `k`. -/
  x : ℕ → E
  /-- Subgradients of the loss functions at the iterates. -/
  g : ℕ → E
  /-- The learning rate is positive. -/
  hη_pos : 0 < η
  /-- Every iterate lies in `C`. -/
  hx_mem : ∀ k, x k ∈ C
  /-- FTRL first-order optimality condition. -/
  hopt : ∀ k, k < K → ∀ y ∈ C,
    (0 : ℝ) ≤ ⟪η • g k + (gradφ (x (k + 1)) - gradφ (x k)), y - x (k + 1)⟫_ℝ
  /-- 1-strong convexity of `φ`: `D_φ(a, b) ≥ ½ ‖a − b‖²`. -/
  hstrong : ∀ a b, ‖a - b‖ ^ 2 / 2 ≤ bregmanDiv φ gradφ a b

-- ============================================================================
-- FTRL step and regret
-- ============================================================================

/-- The FTRL iterate at step `k + 1`.
    Formally, `ftrl_step S k = S.x (k + 1)`, characterised by the optimality
    condition `S.hopt`. -/
def FTRLSetup.ftrl_step (S : FTRLSetup E) (k : ℕ) : E := S.x (k + 1)

/-- Linearised regret against comparator `u`:
    `R_K(u) = Σ_{k<K} ⟨g_k, x_k − u⟩`. -/
def FTRLSetup.regret (S : FTRLSetup E) (u : E) : ℝ :=
  ∑ k ∈ Finset.range S.K, ⟪S.g k, S.x k - u⟫_ℝ

end
