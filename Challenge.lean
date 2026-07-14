import Colorexpanders.Base

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Theorem 4.1 (Large bottom rank implies large top rank).** -/
theorem large_bottom_rank_implies_large_top_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ)
    {t : ℕ} (hBottom : bottomThresholdRank A hHerm μ ≥ t)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (topThresholdRank A hHerm ((μ^(2 : ℕ) - σ) / (1 - σ)) : ℝ)
      ≥ σ^2 * (t : ℝ) := by
  sorry

/-- **Corollary 4.2 (Small top rank implies small bottom rank).** -/
theorem small_top_rank_implies_small_bottom_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {τ : ℝ} (hτ : 0 ≤ τ) {s : ℕ}
    (htop : topThresholdRank A hHerm τ ≤ s)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (bottomThresholdRank A hHerm (Real.sqrt (σ + τ * (1 - σ))) : ℝ)
      ≤ s / (σ^2) := by
  sorry

end ThresholdRank
