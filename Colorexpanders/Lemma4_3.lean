import ColorexpandersLean.Base

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-!
### Lemma 4.3 / Lemma A.1

This is the “PSD witness ⇒ large top threshold rank” lemma.
We assume the eigenvalues are already known to lie in `[-1,1]`, and later
we will derive that from `‖A‖ ≤ 1` for the operator norm.
-/

section Lemma4_3

variable (A M : Matrix n n ℝ)
variable (hA : A.IsHermitian)

/-- **Lemma 4.3 / Lemma A.1.**

Let `A` be Hermitian with eigenvalues in `[-1,1]`. Suppose there exists a
positive semidefinite matrix `M` such that

* `frobeniusInner A M ≥ 1 - ε`,
* `frobeniusSq M ≤ 1 / r`,
* `Matrix.trace M = 1`,

for some `ε ≥ 0`, `r > 0`. Then, for any `C > 1`, the top threshold rank
of `A` at `1 - C⋅ε` is at least `(1 - 1/C)^2 r` (as a real inequality via coercion).
-/
theorem lemma4_3
    (hSpec : eigenvaluesBounded A hA)
    (hMpsd : Matrix.PosSemidef M)
    (hTr : Matrix.trace M = 1)
    {ε r : ℝ} (hr : 0 < r)
    (hInner : frobeniusInner A M ≥ 1 - ε)
    (hFrob : frobeniusSq M ≤ 1 / r)
    {C : ℝ} (hC : 1 < C) :
    ((topThresholdRank A hA (1 - C * ε)) : ℝ) ≥ (1 - 1 / C)^2 * r := by
  classical
  -- Unitary diagonalization of `A`.
  let Uunit := hA.eigenvectorUnitary
  let U : Matrix n n ℝ := Uunit
  have hU : U ∈ Matrix.unitaryGroup n ℝ := Uunit.property
  let d : n → ℝ := hA.eigenvalues
  have hA_decomp : A = U * Matrix.diagonal (fun i => d i) * Uᴴ := by
    have hspec := hA.spectral_theorem
    change A = (Uunit : Matrix n n ℝ) * _ * _ at hspec
    simpa [U, d, Matrix.conjTranspose] using hspec

  -- Conjugate `M` into the eigenbasis.
  let M' : Matrix n n ℝ := Uᴴ * M * U
  have hMpsd' : Matrix.PosSemidef M' :=
    hMpsd.conjTranspose_mul_mul_same (B := U)

  -- Trace and Frobenius invariance.
  have hTr' : Matrix.trace M' = 1 := by
    have := trace_conjUnitary (n := n) (U := U) (hU := hU) (A := M)
    simpa [M'] using this.trans hTr
  have hFrob' : frobeniusSq M' = frobeniusSq M :=
    frobeniusSq_conjUnitary (n := n) (U := U) (hU := hU) (M := M)

  -- Inner product in the eigenbasis.
  have hInner_diag :
      frobeniusInner A M = ∑ i, d i * M' i i :=
    frobeniusInner_diagonalization (n := n)
      (U := U) (hU := hU) (d := d) (A := A) (M := M) hA_decomp hA

  -- Diagonal entries are nonnegative and sum to 1.
  have hdiag_nonneg : ∀ i, 0 ≤ M' i i := fun i => posSemidef_diag_nonneg hMpsd' i
  have hdiag_sum : ∑ i, M' i i = 1 := by simpa [Matrix.trace] using hTr'

  -- Eigenvalues are bounded by 1 in absolute value, so d i ≤ 1.
  have hlam_le_one : ∀ i, d i ≤ 1 := fun i => (abs_le.mp (hSpec i)).2

  -- Lower bound on the spectral sum from the hypothesis.
  have hInner_lower : 1 - ε ≤ ∑ i, d i * M' i i := by
    linarith [hInner_diag, hInner]

  -- The spectral sum cannot exceed 1, so ε ≥ 0.
  have hsum_le_one : ∑ i, d i * M' i i ≤ 1 := by
    have hterm :
        ∀ i ∈ (Finset.univ : Finset n), d i * M' i i ≤ (1 : ℝ) * M' i i := by
      intro i hi; exact mul_le_mul_of_nonneg_right (hlam_le_one i) (hdiag_nonneg i)
    have := Finset.sum_le_sum hterm
    simpa [hdiag_sum] using this
  have hε_nonneg : 0 ≤ ε := by nlinarith [hInner_diag, hInner_lower, hsum_le_one]

  -- Threshold and mass above the threshold.
  set τ : ℝ := 1 - C * ε
  let S : Finset n := Finset.univ.filter (fun i => τ ≤ d i)
  let p : ℝ := ∑ i ∈ S, M' i i

  -- Mass on the complement of `S`.
  have hcomp_diag_sum :
      ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 1 - p := by
    classical
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i => τ ≤ d i) (f := fun i => M' i i)
    have hsplit' :
        ∑ i ∈ S, M' i i +
          ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 1 := by
      simpa [S, hdiag_sum] using hsplit
    linarith

  -- Split the spectral sum at the threshold τ to bound it from above.
  have hsum_split_le :
      ∑ i, d i * M' i i ≤ p + τ * (1 - p) := by
    classical
    let Sc : Finset n := Finset.univ.filter (fun i => ¬ τ ≤ d i)
    have hsplit :=
      Finset.sum_filter_add_sum_filter_not
        (s := Finset.univ) (p := fun i => τ ≤ d i) (f := fun i => d i * M' i i)
    have hsplit' :
        ∑ i, d i * M' i i =
          ∑ i ∈ S, d i * M' i i + ∑ i ∈ Sc, d i * M' i i := by
      simpa [S, Sc] using hsplit.symm
    have hS_le : ∑ i ∈ S, d i * M' i i ≤ p := by
      have hS_le' :
          ∑ i ∈ S, d i * M' i i ≤ ∑ i ∈ S, (1 : ℝ) * M' i i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hdi_le : d i ≤ 1 := hlam_le_one i
        have hM : 0 ≤ M' i i := hdiag_nonneg i
        have hterm := mul_le_mul_of_nonneg_right hdi_le hM
        simpa using hterm
      simpa [p] using hS_le'
    have hSc_le :
        ∑ i ∈ Sc, d i * M' i i ≤ τ * (1 - p) := by
      have hSc_le' :
          ∑ i ∈ Sc, d i * M' i i ≤ ∑ i ∈ Sc, τ * M' i i := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hnot : ¬ τ ≤ d i := (Finset.mem_filter.mp hi).2
        have hdi_le : d i ≤ τ := le_of_lt (lt_of_not_ge hnot)
        have hM : 0 ≤ M' i i := hdiag_nonneg i
        have hterm := mul_le_mul_of_nonneg_right hdi_le hM
        simpa using hterm
      have hsum_tau :
          ∑ i ∈ Sc, τ * M' i i = τ * ∑ i ∈ Sc, M' i i := by
        classical
        simpa using (Finset.mul_sum (a := τ) (s := Sc) (f := fun i => M' i i)).symm
      have hcomp_sum : ∑ i ∈ Sc, M' i i = 1 - p := by
        simpa [Sc] using hcomp_diag_sum
      calc
        ∑ i ∈ Sc, d i * M' i i ≤ ∑ i ∈ Sc, τ * M' i i := hSc_le'
        _ = τ * (1 - p) := by simp [hsum_tau, hcomp_sum]
    calc
      ∑ i, d i * M' i i
          = ∑ i ∈ S, d i * M' i i + ∑ i ∈ Sc, d i * M' i i := hsplit'
      _ ≤ p + τ * (1 - p) := add_le_add hS_le hSc_le

  -- Combine the lower and upper bounds on the spectral sum.
  have hineq : C * ε * (1 - p) ≤ ε := by
    have h := le_trans hInner_lower hsum_split_le
    have hrewrite : p + τ * (1 - p) = 1 - C * ε * (1 - p) := by
      unfold τ
      ring
    linarith [h, hrewrite]

  -- Lower bound on the mass `p` in the super-level set `S`.
  have hp_lower : 1 - 1 / C ≤ p := by
    by_cases hε0 : ε = 0
    · subst hε0
      have hsum_eq : ∑ i, d i * M' i i = 1 := by
        have hlow : (1 : ℝ) ≤ ∑ i, d i * M' i i := by simpa using hInner_lower
        exact le_antisymm hsum_le_one hlow
      have hprod_zero :
          ∀ i, (1 - d i) * M' i i = 0 :=
        by
          classical
          have hdiff_sum :
              ∑ i, (1 - d i) * M' i i = 0 := by
            have hrewrite :
                ∑ i, (1 - d i) * M' i i =
                  (∑ i, M' i i) - ∑ i, d i * M' i i := by
              have h1 :
                  ∑ i, (1 - d i) * M' i i =
                    ∑ i, (M' i i - d i * M' i i) := by
                refine Finset.sum_congr rfl ?_ ; intro i hi; ring
              have h2 :
                  ∑ i, (M' i i - d i * M' i i) =
                    (∑ i, M' i i) - ∑ i, d i * M' i i := by
                simp [Finset.sum_sub_distrib]
              exact h1.trans h2
            calc
              ∑ i, (1 - d i) * M' i i = (∑ i, M' i i) - ∑ i, d i * M' i i := hrewrite
              _ = 1 - 1 := by simp [hdiag_sum, hsum_eq]
              _ = 0 := by ring
          have hnonneg' :
              ∀ i ∈ (Finset.univ : Finset n), 0 ≤ (1 - d i) * M' i i := by
            intro i hi; exact mul_nonneg (by linarith [hlam_le_one i]) (hdiag_nonneg i)
          have hzero :
              ∀ i ∈ (Finset.univ : Finset n), (1 - d i) * M' i i = 0 :=
            (Finset.sum_eq_zero_iff_of_nonneg hnonneg').1 hdiff_sum
          intro i; exact hzero i (Finset.mem_univ i)
      have hτ1 : τ = 1 := by simp [τ]
      have hcomp_zero :
          ∀ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 0 := by
        intro i hi
        have hnot : ¬ τ ≤ d i := (Finset.mem_filter.mp hi).2
        have hcases := mul_eq_zero.mp (hprod_zero i)
        have hne : (1 - d i) ≠ 0 := by linarith [hτ1, hnot]
        exact (hcases.resolve_left hne)
      have hcomp_sum_zero :
          ∑ i ∈ Finset.univ.filter (fun i => ¬ τ ≤ d i), M' i i = 0 := by
        classical
        refine (Finset.sum_eq_zero_iff_of_nonneg ?_).2 hcomp_zero
        intro i hi; exact hdiag_nonneg i
      have hp_one : p = 1 := by linarith [hcomp_diag_sum, hcomp_sum_zero]
      have hCinv_nonneg : 0 ≤ (1 / C : ℝ) := by
        have hCpos : 0 < C := lt_trans (show (0 : ℝ) < 1 by norm_num) hC
        have hCpos' : (0 : ℝ) ≤ C := le_of_lt hCpos
        exact one_div_nonneg.mpr hCpos'
      have hbound : 1 - 1 / C ≤ (1 : ℝ) := by linarith
      linarith [hp_one, hbound]
    · have hεpos : 0 < ε := lt_of_le_of_ne hε_nonneg (by simpa [eq_comm] using hε0)
      have hCpos : 0 < C := lt_trans (show (0 : ℝ) < 1 by norm_num) hC
      have hdiv : 1 - p ≤ 1 / C := by
        have hstep1 :
            C * (1 - p) ≤ 1 := by
          have hmult :=
            (mul_le_mul_of_nonneg_right hineq
              (inv_nonneg.mpr (le_of_lt hεpos)))
          have hmult' : (C * ε * (1 - p)) * ε⁻¹ = C * (1 - p) := by
            field_simp [ne_of_gt hεpos, mul_comm, mul_left_comm, mul_assoc]
          have hright : ε * ε⁻¹ = (1 : ℝ) := by field_simp [ne_of_gt hεpos]
          have hmult'' : C * ε * (1 - p) * ε⁻¹ ≤ 1 := by
            simpa [hright] using hmult
          simpa [hmult'] using hmult''
        have hmult :=
          (mul_le_mul_of_nonneg_right hstep1
            (inv_nonneg.mpr (le_of_lt hCpos)))
        have hright : (1 : ℝ) * C⁻¹ = 1 / C := by
          field_simp [ne_of_gt hCpos]
        have hmult' : C * (1 - p) * C⁻¹ ≤ 1 / C := by
          simpa [hright, mul_assoc] using hmult
        have hleft : (C * (1 - p)) * C⁻¹ = 1 - p := by
          field_simp [ne_of_gt hCpos, mul_comm, mul_left_comm, mul_assoc]
        simpa [hleft] using hmult'
      linarith

  have hp_nonneg : 0 ≤ p := by
    classical
    simpa [p] using Finset.sum_nonneg (fun i _ => hdiag_nonneg i)

  have hCS :
      p ≤ Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2) := by
    classical
    have h :=
      Real.sum_mul_le_sqrt_mul_sqrt (s := S) (f := fun _ => (1 : ℝ)) (g := fun i => M' i i)
    simpa [p, pow_two] using h
  have hCS_sq :
      p^2 ≤ (S.card : ℝ) * ∑ i ∈ S, (M' i i)^2 := by
    classical
    have hnonneg :
        0 ≤ Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2) := by nlinarith
    have hR_abs :
        |Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2)|
          = Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2) :=
      abs_of_nonneg hnonneg
    have hp_abs : |p| = p := abs_of_nonneg hp_nonneg
    have hsq :
        p^2 ≤ (Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2))^2 := by
      have habs :
          |p| ≤ |Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2)| := by
        simpa [hp_abs, hR_abs] using hCS
      have := sq_le_sq.mpr habs
      simpa [pow_two] using this
    have hsum_nonneg : 0 ≤ ∑ i ∈ S, (M' i i)^2 := by positivity
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsimp :
        (Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2))^2 =
          (S.card : ℝ) * ∑ i ∈ S, (M' i i)^2 := by
      calc
        (Real.sqrt (S.card) * Real.sqrt (∑ i ∈ S, (M' i i)^2))^2
            = Real.sqrt (S.card)^2 *
                Real.sqrt (∑ i ∈ S, (M' i i)^2)^2 := by ring
        _ = (S.card : ℝ) * ∑ i ∈ S, (M' i i)^2 := by
              simp [Real.sq_sqrt hcard_nonneg, Real.sq_sqrt hsum_nonneg]
    simpa [hsimp] using hsq

  have hdiag_sq_le :
      ∑ i ∈ S, (M' i i)^2 ≤ frobeniusSq M' := by
    classical
    have hrow :
        ∀ i, (M' i i)^2 ≤ ∑ j, (M' i j)^2 := by
      intro i
      have hsum :
          ∑ j, (M' i j)^2 = (M' i i)^2 +
              ∑ j ∈ Finset.univ.erase i, (M' i j)^2 := by
        have h := Finset.sum_erase_add (s := Finset.univ) (a := i)
          (f := fun j => (M' i j)^2) (Finset.mem_univ i)
        linarith
      have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, (M' i j)^2 := by positivity
      linarith
    have hsum_rows :
        ∑ i ∈ S, (M' i i)^2 ≤ ∑ i ∈ S, ∑ j, (M' i j)^2 := by
      refine Finset.sum_le_sum fun i _ => ?_
      simpa using hrow i
    let Sc : Finset n := Finset.univ.filter (fun i => ¬ τ ≤ d i)
    have hsplit_rows :
        ∑ i, ∑ j, (M' i j)^2 =
          ∑ i ∈ S, ∑ j, (M' i j)^2 +
            ∑ i ∈ Sc, ∑ j, (M' i j)^2 := by
      classical
      have :=
        Finset.sum_filter_add_sum_filter_not
          (s := Finset.univ) (p := fun i => τ ≤ d i) (f := fun i => ∑ j, (M' i j)^2)
      simpa [S, Sc] using this.symm
    have hcomp_nonneg :
        0 ≤ ∑ i ∈ Sc, ∑ j, (M' i j)^2 := by
      refine Finset.sum_nonneg ?_ ; intro i hi
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hsum_total :
        ∑ i ∈ S, ∑ j, (M' i j)^2 ≤ frobeniusSq M' := by
      have htotal : frobeniusSq M' = ∑ i, ∑ j, (M' i j)^2 := rfl
      linarith [hsplit_rows, hcomp_nonneg, htotal]
    exact le_trans hsum_rows hsum_total

  have hCS_sq' :
      p^2 ≤ (S.card : ℝ) * frobeniusSq M' := by
    have hcard_nonneg : 0 ≤ (S.card : ℝ) := by exact_mod_cast Nat.zero_le _
    have hbound :=
      mul_le_mul_of_nonneg_left hdiag_sq_le hcard_nonneg
    exact le_trans hCS_sq hbound

  have hFrob'' : frobeniusSq M' ≤ 1 / r := by
    simpa [hFrob'] using hFrob
  have hcard_bound :
      p^2 * r ≤ (S.card : ℝ) := by
    have hmul :=
      mul_le_mul_of_nonneg_right hCS_sq' (le_of_lt hr)
    have hbound :=
      mul_le_mul_of_nonneg_left hFrob'' (by positivity : 0 ≤ (S.card : ℝ))
    have hbound' :
        (S.card : ℝ) * frobeniusSq M' * r ≤ (S.card : ℝ) := by
      have hr_ne : (r : ℝ) ≠ 0 := ne_of_gt hr
      have hmul' := mul_le_mul_of_nonneg_right hbound (le_of_lt hr)
      have hsimpa : (S.card : ℝ) * (1 / r) * r = (S.card : ℝ) := by
        field_simp [hr_ne]
      have hmul'' :
          (S.card : ℝ) * frobeniusSq M' * r ≤
            (S.card : ℝ) * (1 / r) * r := by
        simpa [mul_assoc] using hmul'
      linarith
    have hmul_simp :
        p^2 * r ≤ (S.card : ℝ) * frobeniusSq M' * r := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    exact le_trans hmul_simp hbound'

  have hp_sq : (1 - 1 / C)^2 ≤ p^2 := by
    have hpos : 0 ≤ 1 - 1 / C := by
      have hCpos : 0 < C := lt_trans (show (0 : ℝ) < 1 by norm_num) hC
      have hCge : (1 : ℝ) ≤ C := le_of_lt hC
      have hinv_le_one : 1 / C ≤ (1 : ℝ) := by
        have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hCge
        simpa using h
      linarith
    nlinarith [hp_lower, hp_nonneg, hpos]

  have hfinal :
      (1 - 1 / C)^2 * r ≤ (S.card : ℝ) := by
    have hr_nonneg : 0 ≤ r := le_of_lt hr
    have hp_sq' := mul_le_mul_of_nonneg_right hp_sq hr_nonneg
    exact le_trans hp_sq' hcard_bound

  have hS_card_nat :
      topThresholdRank A hA τ = S.card := by
    classical
    have hmem :
        ∀ i, i ∈ Finset.univ.filter (fun i => τ ≤ hA.eigenvalues i) ↔
          i ∈ {i | τ ≤ hA.eigenvalues i} := by
      intro i; simp
    have hcard :
        Fintype.card { i | τ ≤ hA.eigenvalues i } =
          (Finset.univ.filter (fun i => τ ≤ hA.eigenvalues i)).card :=
      Fintype.card_of_finset' (s := Finset.univ.filter (fun i => τ ≤ hA.eigenvalues i))
        (p := { i | τ ≤ hA.eigenvalues i }) hmem
    simpa [topThresholdRank, S, d] using hcard

  have hfinal' :
      (1 - 1 / C)^2 * r ≤ (topThresholdRank A hA τ : ℝ) := by
    have hS_cast : (S.card : ℝ) = (topThresholdRank A hA τ : ℝ) := by
      exact_mod_cast hS_card_nat.symm
    simpa [hS_cast] using hfinal

  have hfinal'' :
      (topThresholdRank A hA τ : ℝ) ≥ (1 - 1 / C)^2 * r := by linarith
  simpa [τ] using hfinal''

end Lemma4_3

end ThresholdRank
