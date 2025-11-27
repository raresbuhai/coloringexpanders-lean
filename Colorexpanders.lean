import Colorexpanders.Base
import Colorexpanders.Lemma4_3
import Colorexpanders.Lemma4_4

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Theorem 4.1 (Large bottom rank implies large top rank).**

Includes the trivial `t = 0` case. -/
theorem large_bottom_rank_implies_large_top_rank
    [Nonempty n] (A : Matrix n n ℝ)
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ)
    {t : ℕ} (hBottom : bottomThresholdRank A hHerm μ ≥ t)
    {σ : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1) :
    (topThresholdRank A hHerm ((μ^(2:ℕ) - σ) / (1 - σ)) : ℝ)
      ≥ σ^2 * (t : ℝ) := by
  classical
  by_cases ht0 : t = 0
  · subst ht0
    have hnonneg :
        0 ≤ (topThresholdRank A hHerm ((μ^(2:ℕ) - σ) / (1 - σ)) : ℝ) := by
      exact_mod_cast Nat.zero_le _
    nlinarith
  · have ht : 0 < t := Nat.pos_of_ne_zero ht0
    obtain ⟨M, hMpsd, hTr, hFrob, hInner⟩ :=
      lemma4_4 (A := A) (n := n) (hHerm := hHerm) (hNonneg := hNonneg)
        (hOp := hOp) (hμ := hμ) (ht := ht) (hBottom := hBottom)

    have hSpec : eigenvaluesBounded A hHerm :=
      eigenvaluesBounded_of_opNorm_le_one (A := A) hHerm hOp

    let ε : ℝ := 1 - μ^(2:ℕ)
    have hInner' : frobeniusInner A M ≥ 1 - ε := by
      have : 1 - ε = μ^(2:ℕ) := by
        unfold ε; ring
      simpa [this] using hInner

    have hr : 0 < (t : ℝ) := by exact_mod_cast ht
    have hFrob' : frobeniusSq M ≤ 1 / (t : ℝ) := hFrob
    set C : ℝ := 1 / (1 - σ) with hCdef

    have hC : 1 < C := by
      have hden : 0 < 1 - σ := sub_pos.mpr hσ₁
      have hlt : 1 - σ < 1 := by linarith
      have hinv : 1 < (1 - σ)⁻¹ := (one_lt_inv₀ hden).2 hlt
      simpa [C, one_div] using hinv

    have hTop :
        (topThresholdRank A hHerm (1 - C * ε) : ℝ)
          ≥ (1 - 1 / C)^2 * (t : ℝ) :=
      lemma4_3 (A := A) (M := M) (n := n) (hA := hHerm)
        hSpec hMpsd hTr (ε := ε) (r := (t : ℝ)) hr hInner' hFrob' (C := C) hC

    have hτ :
        1 - C * ε = (μ^(2:ℕ) - σ) / (1 - σ) := by
      have hden : (1 - σ) ≠ 0 := by
        have hpos : 0 < 1 - σ := sub_pos.mpr hσ₁
        linarith
      have hC : C = (1 - σ)⁻¹ := by simp [C, one_div]
      calc
        1 - C * ε
            = 1 - (1 - σ)⁻¹ * (1 - μ^(2:ℕ)) := by simp [ε, hC]
        _ = ((1 - σ) - (1 - μ^(2:ℕ))) / (1 - σ) := by
          field_simp [hden]
        _ = (μ^(2:ℕ) - σ) / (1 - σ) := by ring

    have hσsq :
        (1 - 1 / C)^2 = σ^2 := by
      have hinv : 1 / C = 1 - σ := by
        simp [C, one_div]
      calc
        (1 - 1 / C)^2 = (1 - (1 - σ))^2 := by simp [hinv]
        _ = σ^2 := by ring
    have hσsq' : (1 - C⁻¹)^2 = σ^2 := by simpa [one_div] using hσsq

    have hTop' : σ^2 * (t : ℝ) ≤
        (topThresholdRank A hHerm ((μ^(2:ℕ) - σ) / (1 - σ)) : ℝ) := by
      have := hTop
      simpa [hτ, hσsq', mul_comm, mul_left_comm, mul_assoc] using this
    linarith

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
  classical
  set μ : ℝ := Real.sqrt (σ + τ * (1 - σ)) with hμdef
  have hμ_nonneg : 0 ≤ μ := by simp [hμdef]
  have hμ_sq : μ^(2:ℕ) = σ + τ * (1 - σ) := by
    have hpos : 0 ≤ σ + τ * (1 - σ) := by
      have hσnonneg : 0 ≤ σ := le_of_lt hσ₀
      have h1σ : 0 ≤ 1 - σ := sub_nonneg.mpr (le_of_lt hσ₁)
      nlinarith
    have h := Real.sq_sqrt hpos
    simpa [hμdef] using h
  have hden : 1 - σ ≠ 0 := by linarith
  have hτ_from_μ :
      (μ^(2:ℕ) - σ) / (1 - σ) = τ := by
    have hμ_sq' : μ^(2:ℕ) - σ = τ * (1 - σ) := by
      calc
        μ^(2:ℕ) - σ = (σ + τ * (1 - σ)) - σ := by nlinarith [hμ_sq]
        _ = τ * (1 - σ) := by ring
    calc
      (μ^(2:ℕ) - σ) / (1 - σ) = (τ * (1 - σ)) / (1 - σ) := by simp [hμ_sq']
      _ = τ := by field_simp [hden]

  have htop_real : (topThresholdRank A hHerm τ : ℝ) ≤ s := by exact_mod_cast htop
  have hσ2_pos : 0 < σ^2 := by nlinarith

  by_cases hbr0 : bottomThresholdRank A hHerm μ = 0
  · have hs_nonneg : 0 ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le _
    have hσ_nonneg : 0 ≤ σ^2 := le_of_lt hσ2_pos
    have hres : (0 : ℝ) ≤ s / σ^2 := by
      exact div_nonneg hs_nonneg hσ_nonneg
    simpa [hbr0] using hres
  · have htop_lower :
        (topThresholdRank A hHerm ((μ^(2:ℕ) - σ) / (1 - σ)) : ℝ) ≥
          σ^2 * (bottomThresholdRank A hHerm μ : ℝ) := by
      simpa using
        (large_bottom_rank_implies_large_top_rank (A := A) (n := n)
          (hHerm := hHerm) (hNonneg := hNonneg) (hOp := hOp)
          (hμ := hμ_nonneg) (hBottom := le_rfl)
          (σ := σ) hσ₀ hσ₁)
    have htop_lower' :
        (topThresholdRank A hHerm τ : ℝ) ≥
          σ^2 * (bottomThresholdRank A hHerm μ : ℝ) := by
      simpa [hτ_from_μ] using htop_lower
    have hmul_le_s : σ^2 * (bottomThresholdRank A hHerm μ : ℝ) ≤ s := by
      linarith [htop_real, htop_lower']
    have hres : (bottomThresholdRank A hHerm μ : ℝ) ≤ s / σ^2 := by
      have hσpos : 0 < σ^2 := hσ2_pos
      have hmul_le_s' :
          (bottomThresholdRank A hHerm μ : ℝ) * σ^2 ≤ s := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_le_s
      exact (le_div_iff₀ hσpos).2 hmul_le_s'
    exact hres

#print axioms large_bottom_rank_implies_large_top_rank
#print axioms small_top_rank_implies_small_bottom_rank

end ThresholdRank
