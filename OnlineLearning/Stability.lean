import Mathlib
import OnlineLearning.Defs

/-!
# Online Learning: Stability

Algebraic identities for Bregman divergence and per-step stability bounds
for the FTRL iterates.

## Main results

* `bregmanDiv_self` — `D_φ(x, x) = 0`
* `bregman_nonneg` — `0 ≤ D_φ(a, b)` from 1-strong convexity
* `bregman_three_point` — three-point identity for Bregman divergence
* `regret_decomposition` — regret = stability terms + approximation terms
* `ftrl_stability` — per-step stability bound via completing the square
-/

noncomputable section

open Finset
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
============================================================================
Bregman divergence identities
============================================================================

Bregman divergence vanishes at equal points: `D_φ(x, x) = 0`.
-/
@[simp]
lemma bregmanDiv_self (φ : E → ℝ) (gradφ : E → E) (x : E) :
    bregmanDiv φ gradφ x x = 0 := by
  unfold bregmanDiv; simp +decide ;

/-
Bregman divergence is non-negative under 1-strong convexity.
-/
lemma FTRLSetup.bregman_nonneg (S : FTRLSetup E) (a b : E) :
    0 ≤ bregmanDiv S.φ S.gradφ a b := by
  exact le_trans ( by positivity ) ( S.hstrong a b )

/-
Three-point identity for Bregman divergence:
    `D_φ(a, c) = D_φ(a, b) + D_φ(b, c) + ⟨∇φ(b) − ∇φ(c), a − b⟩`.
-/
lemma bregman_three_point (φ : E → ℝ) (gradφ : E → E) (a b c : E) :
    bregmanDiv φ gradφ a c =
      bregmanDiv φ gradφ a b + bregmanDiv φ gradφ b c +
        ⟪gradφ b - gradφ c, a - b⟫_ℝ := by
  unfold bregmanDiv;
  simp +decide [ inner_sub_left, inner_sub_right ] ; ring

/-
============================================================================
Regret decomposition
============================================================================

Pointwise regret split:
    `⟨g, x − u⟩ = ⟨g, x − y⟩ + ⟨g, y − u⟩`.
-/
lemma inner_sub_split (g x y u : E) :
    ⟪g, x - u⟫_ℝ = ⟪g, x - y⟫_ℝ + ⟪g, y - u⟫_ℝ := by
  rw [ ← inner_add_right, sub_add_sub_cancel ]

/-
**Regret decomposition** into stability and approximation terms:
    `Σ ⟨g_k, x_k − u⟩ = Σ ⟨g_k, x_k − x_{k+1}⟩ + Σ ⟨g_k, x_{k+1} − u⟩`.
-/
theorem regret_decomposition (S : FTRLSetup E) (u : E) :
    S.regret u =
      (∑ k ∈ Finset.range S.K, ⟪S.g k, S.x k - S.x (k + 1)⟫_ℝ) +
      (∑ k ∈ Finset.range S.K, ⟪S.g k, S.x (k + 1) - u⟫_ℝ) := by
  rw [ ← Finset.sum_add_distrib, FTRLSetup.regret ];
  simp +decide [ inner_sub_right ]

/-
============================================================================
Per-step stability
============================================================================

**FTRL stability** (per-step bound via completing the square):
    `η ⟨g_k, x_k − x_{k+1}⟩ − D_φ(x_{k+1}, x_k) ≤ η² ‖g_k‖² / 2`.

    Combined with the approximation bound this yields the Bregman regret bound.
    The proof uses 1-strong convexity (`D_φ(a,b) ≥ ½‖a−b‖²`) and the
    completing-the-square identity
    `η⟨g,v⟩ − ‖v‖²/2 = η²‖g‖²/2 − ‖v − ηg‖²/2 ≤ η²‖g‖²/2`.
-/
theorem ftrl_stability (S : FTRLSetup E) (k : ℕ) :
    S.η * ⟪S.g k, S.x k - S.x (k + 1)⟫_ℝ -
      bregmanDiv S.φ S.gradφ (S.x (k + 1)) (S.x k) ≤
    S.η ^ 2 / 2 * ‖S.g k‖ ^ 2 := by
  -- Applying the completing-the-square identity:
  -- `‖(x_k - x_{k+1}) - η•g‖² ≥ 0, expanding gives ‖x_k - x_{k+1}‖² - 2η⟨g, x_k - x_{k+1}⟩ + η²‖g‖² ≥ 0`.
  have h_complete_square : ‖S.x k - S.x (k + 1) - S.η • S.g k‖ ^ 2 ≥ 0 := by
    positivity;
  simp_all +decide [ bregmanDiv, norm_sub_sq_real ];
  simp_all +decide [ norm_smul, real_inner_comm ];
  have := S.hstrong ( S.x ( k + 1 ) ) ( S.x k ) ; simp_all +decide [ bregmanDiv, norm_sub_sq_real, real_inner_smul_right ] ;
  rw [ abs_of_pos S.hη_pos ] at h_complete_square ; linarith [ real_inner_comm ( S.x ( k + 1 ) ) ( S.x k ) ] ;

end