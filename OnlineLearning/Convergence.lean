import Mathlib
import OnlineLearning.Stability

/-!
# Online Learning: Convergence

Main regret bounds for FTRL: the Bregman regret bound, the bounded-gradient
regret bound, and the `O(√K)` convergence rate with the optimal learning rate.

## Main results

* `approximation_bound` — per-step approximation term from FTRL optimality
* `bregman_regret_bound` — `Σ ⟨g_k, x_k−u⟩ ≤ D_φ(u,x₀)/η + η/2 Σ‖g_k‖²`
* `ftrl_regret_bound` — `regret ≤ D₀/η + ηKG²/2`
* `ftrl_convergence` — with optimal η, `regret ≤ G√(2D₀K)`
-/

noncomputable section

open Finset
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-
============================================================================
Approximation bound
============================================================================

**Approximation bound** from FTRL optimality and the three-point identity:
    `η ⟨g_k, x_{k+1} − u⟩ ≤ D_φ(u, x_k) − D_φ(u, x_{k+1}) − D_φ(x_{k+1}, x_k)`.
-/
lemma approximation_bound (S : FTRLSetup E) (k : ℕ) (hk : k < S.K)
    (u : E) (hu : u ∈ S.C) :
    S.η * ⟪S.g k, S.x (k + 1) - u⟫_ℝ ≤
      bregmanDiv S.φ S.gradφ u (S.x k) -
        bregmanDiv S.φ S.gradφ u (S.x (k + 1)) -
        bregmanDiv S.φ S.gradφ (S.x (k + 1)) (S.x k) := by
  have := S.hopt k hk u hu;
  norm_num [ inner_add_left, inner_sub_left, inner_smul_left ] at *;
  norm_num [ bregmanDiv, inner_sub_left, inner_sub_right ] at *;
  linarith

/-
============================================================================
Combined per-step bound
============================================================================

Combined per-step regret bound:
    `η ⟨g_k, x_k − u⟩ ≤ D_φ(u, x_k) − D_φ(u, x_{k+1}) + η²/2 ‖g_k‖²`.
-/
lemma combined_per_step (S : FTRLSetup E) (k : ℕ) (hk : k < S.K)
    (u : E) (hu : u ∈ S.C) :
    S.η * ⟪S.g k, S.x k - u⟫_ℝ ≤
      bregmanDiv S.φ S.gradφ u (S.x k) -
        bregmanDiv S.φ S.gradφ u (S.x (k + 1)) +
      S.η ^ 2 / 2 * ‖S.g k‖ ^ 2 := by
  rw [ inner_sub_split ];
  swap;
  exact S.x ( k + 1 );
  linarith [ approximation_bound S k hk u hu, ftrl_stability S k ]

/-
============================================================================
Bregman regret bound
============================================================================

Scaled regret bound (before dividing by η):
    `η · regret(u) ≤ D_φ(u, x₀) + η²/2 · Σ ‖g_k‖²`.
-/
lemma scaled_regret_bound (S : FTRLSetup E) (u : E) (hu : u ∈ S.C) :
    S.η * S.regret u ≤
      bregmanDiv S.φ S.gradφ u (S.x 0) +
      S.η ^ 2 / 2 * ∑ k ∈ Finset.range S.K, ‖S.g k‖ ^ 2 := by
  -- Apply the combined_per_step lemma to each term in the sum.
  have h_sum : ∑ k ∈ Finset.range S.K, (S.η * ⟪S.g k, S.x k - u⟫_ℝ) ≤ ∑ k ∈ Finset.range S.K, (bregmanDiv S.φ S.gradφ u (S.x k) - bregmanDiv S.φ S.gradφ u (S.x (k + 1)) + S.η ^ 2 / 2 * ‖S.g k‖ ^ 2) := by
    exact Finset.sum_le_sum fun k hk => combined_per_step S k ( Finset.mem_range.mp hk ) u hu;
  convert h_sum.trans _ using 1;
  · rw [ ← Finset.mul_sum _ _ _, FTRLSetup.regret ];
  · rw [ Finset.sum_add_distrib, Finset.mul_sum _ _ _ ];
    rw [ Finset.sum_range_sub' ] ; norm_num;
    exact S.bregman_nonneg _ _

/-
**Bregman regret bound**:
    `Σ ⟨g_k, x_k − u⟩ ≤ D_φ(u, x₀)/η + η/2 · Σ ‖g_k‖²`.
-/
theorem bregman_regret_bound (S : FTRLSetup E) (u : E) (hu : u ∈ S.C) :
    S.regret u ≤
      bregmanDiv S.φ S.gradφ u (S.x 0) / S.η +
      S.η / 2 * ∑ k ∈ Finset.range S.K, ‖S.g k‖ ^ 2 := by
  rw [ div_add', le_div_iff₀ ] <;> try linarith [ S.hη_pos ];
  convert scaled_regret_bound S u hu using 1 <;> ring

/-
============================================================================
FTRL regret bound with bounded subgradients
============================================================================

**FTRL regret bound** with bounded subgradients:
    If `‖g_k‖ ≤ G` for all `k < K`, then `regret ≤ D_φ(u,x₀)/η + ηKG²/2`.
-/
theorem ftrl_regret_bound (S : FTRLSetup E) (u : E) (hu : u ∈ S.C) (G : ℝ)
    (hG : ∀ k, k < S.K → ‖S.g k‖ ≤ G) :
    S.regret u ≤
      bregmanDiv S.φ S.gradφ u (S.x 0) / S.η +
      S.η * ↑S.K * G ^ 2 / 2 := by
  have := bregman_regret_bound S u hu;
  convert this.trans _;
  rw [ add_le_add_iff_left ];
  convert mul_le_mul_of_nonneg_left ( Finset.sum_le_card_nsmul _ _ _ fun k hk => pow_le_pow_left₀ ( norm_nonneg _ ) ( hG k ( Finset.mem_range.mp hk ) ) 2 ) ( show 0 ≤ S.η / 2 by linarith [ S.hη_pos ] ) using 1 ; norm_num ; ring

/-
============================================================================
O(√K) convergence
============================================================================

**FTRL convergence** with optimal learning rate:
    With `η = √(2D₀ / (K G²))`, the regret satisfies
    `R_K ≤ G √(2 D₀ K)`,
    giving `O(√K)` regret for the worst-case adversary.
-/
theorem ftrl_convergence (S : FTRLSetup E) (u : E) (hu : u ∈ S.C)
    (G D₀ : ℝ) (hG_pos : 0 < G) (hD₀_pos : 0 < D₀) (hK_pos : 0 < S.K)
    (hG : ∀ k, k < S.K → ‖S.g k‖ ≤ G)
    (hD₀ : bregmanDiv S.φ S.gradφ u (S.x 0) ≤ D₀)
    (hη : S.η = Real.sqrt (2 * D₀ / (↑S.K * G ^ 2))) :
    S.regret u ≤ G * Real.sqrt (2 * D₀ * ↑S.K) := by
  refine le_trans ( ftrl_regret_bound S u hu G hG ) ?_;
  convert add_le_add ( div_le_div_of_nonneg_right hD₀ <| hη.symm ▸ Real.sqrt_nonneg _ ) le_rfl using 1 ; rw [ hη ] ; ring_nf;
  -- Simplify the expression by cancelling out common terms.
  field_simp
  ring_nf;
  norm_num [ mul_assoc, mul_comm, mul_left_comm, hG_pos.le, hD₀_pos.le, hK_pos.le ] ; ring_nf;
  norm_num [ hG_pos.ne', hD₀_pos.le, hK_pos.ne' ] ; ring_nf

end