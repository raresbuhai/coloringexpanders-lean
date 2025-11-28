import Colorexpanders.Base
import Colorexpanders.Lemma4_3

open Matrix BigOperators
open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Lemma 4.4

From many negative eigenvalues and `‖A‖ ≤ 1`, build a PSD witness `M`
with the desired properties.
-/

section Lemma4_4

variable (A : Matrix n n ℝ)

/-- Indices of eigenvalues `≤ -μ`, packaged as a finite type. -/
@[simp] abbrev negEigSubtype (μ : ℝ) (hHerm : A.IsHermitian) :=
  { i : n // hHerm.eigenvalues i ≤ -μ }

/-- Choose the first `t` indices among the negative eigenvalues (using an equivalence
with `Fin`). We rely on `hBottom : bottomThresholdRank A hHerm μ ≥ t` to know that
there are at least `t` such indices. -/
noncomputable def negEigIdx
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Fin t → n := fun s =>
  let hcard :
      t ≤ Fintype.card (negEigSubtype (A := A) (n := n) μ hHerm) := by
        simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
  ((Fintype.equivFin (negEigSubtype (A := A) (n := n) μ hHerm)).symm
      (Fin.castLE hcard s)).1

/-- The unscaled matrix whose columns are the selected eigenvectors. -/
noncomputable def negEigMatrix
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n (Fin t) ℝ :=
  fun i s => (hHerm.eigenvectorUnitary : Matrix n n ℝ) i
    (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)

/-- Scaled version of the selected eigenvectors: each column is divided by √t. -/
noncomputable def negEigMatrixScaled
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (_ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n (Fin t) ℝ :=
  fun i s => (1 / Real.sqrt (t : ℝ)) *
    negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i s

/-- Row vector `w_i` in the paper: the `i`-th row of the scaled eigenvector matrix. -/
noncomputable def negRow
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    Fin t → ℝ :=
  fun s => negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s

/-- `‖w_i‖`. -/
noncomputable def negRowNorm
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) : ℝ :=
  Real.sqrt (∑ s, (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s)^2)

/-- The normalized tensor square `v_i` used to build `V`. -/
noncomputable def negVcol
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    Fin t × Fin t → ℝ :=
  fun p =>
    let r := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
    if _hr : r = 0 then 0
    else
      (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p.1 *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p.2) / r

/-- Matrix `V` whose columns are the `v_i`. -/
noncomputable def negVmatrix
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix (Fin t × Fin t) n ℝ :=
  fun p i => negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p

/-- Candidate witness matrix `M = Vᵀ * V`. -/
noncomputable def negWitnessM
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix n n ℝ :=
  (negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ *
    (negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)

-- Rewriting the Frobenius inner product with `negWitnessM` as a trace over `V * A * Vᵀ`.
lemma frobeniusInner_negWitnessM_trace
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
      Matrix.trace
        (negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom *
          A *
          (negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ) := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hA_symm : Matrix.transpose A = A := by
    simpa only using hHerm
  calc
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
        = Matrix.trace (Matrix.transpose A * (Vᵀ * V)) := by
            simp only [negWitnessM, frobeniusInner_trace, V]
    _ = Matrix.trace ((Matrix.transpose A * Vᵀ) * V) := by
            simp only [Matrix.mul_assoc]
    _ = Matrix.trace (V * (Matrix.transpose A * Vᵀ)) := by
            simpa only [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm (A := Matrix.transpose A * Vᵀ) (B := V))
    _ = Matrix.trace (V * A * Vᵀ) := by
            simp only [hA_symm, Matrix.mul_assoc]

-- Cyclic form: over reals, `frobeniusInner A (Vᵀ V) = trace (A * Vᵀ V)`.
lemma frobeniusInner_negWitnessM_cyclic
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
      Matrix.trace (A *
        (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)) := by
  classical
  -- For real symmetric A, `Aᵀ = A` and `frobeniusInner` is `trace (Aᵀ M)`.
  have hA_symm : Matrix.transpose A = A := by
    simpa only using hHerm
  simp only [negWitnessM, frobeniusInner_trace, hA_symm]

/-! ### First properties of the constructed matrices -/

lemma negEigIdx_injective
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Function.Injective (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) := by
  classical
  intro a b h
  -- Unpack the injective pieces: Fin.castLE, the `equivFin` inverse, and subtype coercion.
  have hcard :
      t ≤ Fintype.card (negEigSubtype (A := A) (n := n) μ hHerm) := by
    simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
  let eBad : negEigSubtype (A := A) (n := n)
    μ hHerm ≃ Fin (Fintype.card (negEigSubtype (A := A) (n := n) μ hHerm)) :=
    Fintype.equivFin _
  have hcast_inj : Function.Injective (Fin.castLE hcard) :=
    Fin.castLE_injective hcard
  have hsymm_inj : Function.Injective eBad.symm :=
    (Function.LeftInverse.injective (g := eBad)) (by
      intro x
      exact eBad.right_inv x)
  have hval_inj : Function.Injective (@Subtype.val _ (fun i => hHerm.eigenvalues i ≤ -μ)) :=
    fun x y hxy => Subtype.ext hxy
  -- Compose injective maps.
  exact (hval_inj.comp (hsymm_inj.comp hcast_inj)) h

lemma negEigMatrix_cols_orthonormal
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
      (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) =
      (1 : Matrix (Fin t) (Fin t) ℝ) := by
  classical
  -- `Uᵀ * U = 1` for the unitary eigenvector matrix.
  let U : Matrix n n ℝ := hHerm.eigenvectorUnitary
  have hU_unitary : U ∈ Matrix.unitaryGroup n ℝ := hHerm.eigenvectorUnitary.2
  have hU_mul_right : Uᵀ * U = (1 : Matrix n n ℝ) :=
    by
      -- Use the `Uᴴ * U = 1` characterization of unitarity (for real matrices `ᴴ = ᵀ`).
      have h := (Matrix.mem_unitaryGroup_iff').mp hU_unitary
      simpa only using h
  -- Evaluate each entry explicitly.
  ext s r
  -- Expand the matrix product.
  have hsum :
      ((negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
        (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)) s r =
        ∑ i, negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i s *
          negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i r := by
    simp only [mul_apply, transpose_apply]
  have hU_entry :
      ∑ i, negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i s *
          negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i r
        = (Uᵀ * U) (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)
            (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r) := by
    simp only [negEigMatrix, IsHermitian.eigenvectorUnitary_apply, mul_apply, transpose_apply, U]
  have hdelta :
      (Uᵀ * U) (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)
          (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r)
        = if negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s =
              negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r
            then 1 else 0 := by
    -- Evaluate the `1` matrix entry.
    have := congrArg (fun M => M (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)
      (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r)) hU_mul_right
    simpa only [one_apply] using this
  have hidx_inj := negEigIdx_injective (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom
  have hsr : (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s =
      negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r) ↔ s = r :=
    hidx_inj.eq_iff
  -- Put everything together.
  calc
    ((negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
        negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) s r
        = _ := hsum
    _ = (Uᵀ * U)
          (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)
          (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom r) := hU_entry
    _ = (if s = r then (1 : ℝ) else 0) := by
          simpa only [hsr] using hdelta
    _ = (1 : Matrix (Fin t) (Fin t) ℝ) s r := by
          simp only [one_apply]

lemma negEigMatrixScaled_orthonormal
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ *
      (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
      (1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ) := by
  classical
  -- Factor out the scalar `(1/√t)^2 = 1/t`.
  have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le _
  have hscale : (1 / Real.sqrt (t : ℝ))^2 = 1 / (t : ℝ) := by
    have hsqrt : (Real.sqrt (t : ℝ))^2 = (t : ℝ) := Real.sq_sqrt ht_nonneg
    calc
      (1 / Real.sqrt (t : ℝ))^2 = 1 / (Real.sqrt (t : ℝ))^2 := by ring
      _ = 1 / (t : ℝ) := by simp only [hsqrt, one_div]
  -- Recognize `negEigMatrixScaled` as a global scalar multiple of `negEigMatrix`.
  have hscaled :
      negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom =
        (1 / Real.sqrt (t : ℝ)) •
          negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom := by
    ext i s; simp only [negEigMatrixScaled, one_div, smul_apply, smul_eq_mul]
  calc
    (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ *
        negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
        = ((1 / Real.sqrt (t : ℝ)) • negEigMatrix
          (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
            ((1 / Real.sqrt (t : ℝ)) • negEigMatrix
              (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) := by
          simp only [hscaled, one_div, transpose_smul, Matrix.mul_smul, smul_mul]
    _ = (1 / Real.sqrt (t : ℝ))^2 •
          ((negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
            negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) := by
          simp only [one_div, transpose_smul, Matrix.mul_smul, smul_mul, smul_smul, pow_two]
    _ = (1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ) := by
          simp only [one_div, inv_pow, Nat.cast_nonneg, Real.sq_sqrt,
            negEigMatrix_cols_orthonormal (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom]

/-- Trace of `Usub * Usubᵀ` equals 1 (since the columns are orthonormal up to `1/√t`). -/
lemma negUsub_trace_one
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace
      (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom *
        (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ) = 1 := by
  classical
  let Us := negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have horth := negEigMatrixScaled_orthonormal (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have htrace_swap :
      Matrix.trace (Us * Usᵀ) = Matrix.trace (Usᵀ * Us) :=
    Matrix.trace_mul_comm (A := Us) (B := Usᵀ)
  calc
    Matrix.trace (Us * Usᵀ)
        = Matrix.trace (Usᵀ * Us) := htrace_swap
    _ = Matrix.trace ((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) := by
          simpa only [one_div, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, Us] using
            congrArg Matrix.trace horth
    _ = (1 / (t : ℝ)) * (t : ℝ) := by
          have htcard : (Fintype.card (Fin t) : ℝ) = t := by simp only [Fintype.card_fin]
          simp only [one_div, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, mul_comm]
    _ = 1 := by
          have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
          field_simp [ht']

/-- `‖Usub Usubᵀ‖_F^2 = 1 / t`. -/
lemma negUsub_frobeniusSq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq
      (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom *
        (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)ᵀ)
      = 1 / (t : ℝ) := by
  classical
  let Us := negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have horth := negEigMatrixScaled_orthonormal (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hmul :
      Us * Usᵀ * (Us * Usᵀ) = (1 / (t : ℝ)) • (Us * Usᵀ) := by
    calc
      Us * Usᵀ * (Us * Usᵀ) = Us * (Usᵀ * Us) * Usᵀ := by
        simp only [Matrix.mul_assoc]
      _ = Us * ((1 / (t : ℝ)) • (1 : Matrix (Fin t) (Fin t) ℝ)) * Usᵀ := by
        simpa only [one_div, Matrix.mul_smul, Matrix.mul_one, smul_mul, Us] using
          congrArg (fun M => Us * M * Usᵀ) horth
      _ = (1 / (t : ℝ)) • (Us * Usᵀ) := by
        simp only [one_div, Matrix.mul_smul, Matrix.mul_one, smul_mul]
  calc
    frobeniusSq (Us * Usᵀ)
        = Matrix.trace (Us * Usᵀ * (Us * Usᵀ)) := by
            -- `(Us * Usᵀ)` is symmetric, so its transpose is itself.
            have hsymm : (Us * Usᵀ)ᵀ = Us * Usᵀ := by simp only [transpose_mul,
              transpose_transpose]
            simp only [frobeniusSq_trace, hsymm]
    _ = Matrix.trace ((1 / (t : ℝ)) • (Us * Usᵀ)) := by
          simp only [hmul, one_div, trace_smul, smul_eq_mul]
    _ = (1 / (t : ℝ)) * Matrix.trace (Us * Usᵀ) := by
          simp only [one_div, trace_smul, smul_eq_mul]
    _ = 1 / (t : ℝ) := by
          have htr := negUsub_trace_one (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
          have htr' : Matrix.trace (Us * Usᵀ) = 1 := by simpa only [Us] using htr
          simp only [one_div, htr', mul_one]

-- Tensor-square norm identity.
lemma tensorSquare_sum_sq {t : ℕ} (u : Fin t → ℝ) :
    ∑ p : Fin t × Fin t, (u p.1 * u p.2)^2 = (∑ s : Fin t, (u s)^2)^2 := by
  classical
  -- Rewrite the sum over the product as an iterated sum.
  have hdouble :
      ∑ p : Fin t × Fin t, (u p.1 * u p.2)^2 =
        ∑ i : Fin t, ∑ j : Fin t, (u i * u j)^2 := by
    simpa only [Finset.univ_product_univ] using
      (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f := fun p : Fin t × Fin t =>
        (u p.1 * u p.2) ^ 2))
  -- Convert `(u i * u j)^2` into `(u i)^2 * (u j)^2`.
  have hpow :
      ∑ i : Fin t, ∑ j : Fin t, (u i * u j)^2 =
        ∑ i : Fin t, ∑ j : Fin t, (u i)^2 * (u j)^2 := by
    simp only [mul_pow]
  -- Factor out `(u i)^2` from the inner sum.
  have hfactor :
      ∑ i : Fin t, ∑ j : Fin t, (u i)^2 * (u j)^2 =
        ∑ i : Fin t, (u i)^2 * ∑ j : Fin t, (u j)^2 := by
    refine Finset.sum_congr rfl ?_
    intro i _
    -- `Finset.mul_sum` gives `(u i)^2 * ∑ j, (u j)^2 = ∑ j, (u i)^2 * (u j)^2`.
    -- We use its symmetry to pull out `(u i)^2`.
    have hmul := Finset.mul_sum (a := (u i)^2) (s := Finset.univ) (f := fun j : Fin t => (u j)^2)
    simpa only using hmul.symm
  calc
    ∑ p : Fin t × Fin t, (u p.1 * u p.2)^2
        = ∑ i : Fin t, ∑ j : Fin t, (u i * u j)^2 := hdouble
    _ = ∑ i : Fin t, ∑ j : Fin t, (u i)^2 * (u j)^2 := hpow
    _ = ∑ i : Fin t, (u i)^2 * ∑ j : Fin t, (u j)^2 := hfactor
    _ = (∑ s : Fin t, (u s)^2) * ∑ j : Fin t, (u j)^2 := by
          simp only [Finset.sum_mul]
    _ = (∑ s : Fin t, (u s)^2) ^ 2 := by ring

-- Mixed version: ∑ (u a u b) (v a v b) = (∑ u v)^2.
lemma tensorSquare_sum_mul {t : ℕ} (u v : Fin t → ℝ) :
    ∑ p : Fin t × Fin t, (u p.1 * u p.2) * (v p.1 * v p.2)
      = (∑ s : Fin t, u s * v s) ^ 2 := by
  classical
  classical
  have hdouble :
      ∑ p : Fin t × Fin t, (u p.1 * u p.2) * (v p.1 * v p.2)
        = ∑ i : Fin t, ∑ j : Fin t, (u i * u j) * (v i * v j) := by
    simpa only [Finset.univ_product_univ] using
      (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f := fun p : Fin t × Fin t =>
        (u p.1 * u p.2) * (v p.1 * v p.2)))
  calc
    ∑ p : Fin t × Fin t, (u p.1 * u p.2) * (v p.1 * v p.2)
        = ∑ i : Fin t, ∑ j : Fin t, (u i * u j) * (v i * v j) := hdouble
    _ = ∑ i : Fin t, (u i * v i) * ∑ j : Fin t, (u j * v j) := by
          refine Finset.sum_congr rfl ?_;
            intro i _; simpa only [mul_left_comm, mul_comm, mul_assoc] using
              (Finset.mul_sum (a := u i * v i) (s := Finset.univ) (f := fun j : Fin t =>
                  u j * v j)).symm
    _ = (∑ i : Fin t, u i * v i) * (∑ j : Fin t, u j * v j) := by
          simpa only [mul_assoc] using
            (Finset.sum_mul (s := Finset.univ) (f := fun i : Fin t => u i * v i) (a :=
                ∑ j : Fin t, u j * v j)).symm
    _ = (∑ s : Fin t, u s * v s) ^ 2 := by ring

-- Column norm of `negVcol` matches the row norm of the scaled eigenvector matrix.
lemma negVcol_norm_sq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    ∑ p, (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 =
      ∑ s, (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s)^2 := by
  classical
  -- Shorthand for the row `w_i` and its norm.
  let w : Fin t → ℝ := negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  let r : ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  -- The right-hand side is just `∑ (w s)^2`.
  have hrhs : ∑ s, (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s)^2 =
      ∑ s, (w s)^2 := by rfl
  -- `r^2` is the sum of squares of `w`.
  have hsq :
      r ^ 2 = ∑ s, (w s)^2 := by
    have hnonneg : 0 ≤ ∑ s, (w s)^2 := by positivity
    dsimp only [negRowNorm, w, r] at *
    simpa only [pow_two] using (Real.sq_sqrt hnonneg)
  -- Split on whether the norm is zero.
  by_cases hr : r = 0
  · -- If `r = 0`, then every entry of `v_i` is zero and both sides vanish.
    have hsum_zero : ∑ s, (w s)^2 = 0 := by
      have h' : (0 : ℝ) = ∑ s, (w s)^2 := by simpa only [hr, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow] using hsq
      simpa only using h'.symm
    calc
      ∑ p, (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 = 0 := by
        simp only [negVcol, hr, ↓reduceDIte, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow, Finset.sum_const_zero, r]
      _ = ∑ s, (w s)^2 := by simp only [hsum_zero]
      _ = ∑ s, (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s)^2 := by
        simp only [hrhs]
  · -- If `r ≠ 0`, pull out the normalization factor.
    have hrne : r ≠ 0 := hr
    have hr2_ne : r ^ 2 ≠ 0 := pow_ne_zero _ hrne
    calc
      ∑ p, (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2
          = ∑ p : Fin t × Fin t, (w p.1 * w p.2) ^ 2 * (r ^ 2)⁻¹ := by
              simp only [negVcol, hr, ↓reduceDIte, div_eq_mul_inv, mul_assoc, pow_two,
                mul_left_comm, mul_comm, _root_.mul_inv_rev, w, r]
          _ = (∑ p : Fin t × Fin t, (w p.1 * w p.2) ^ 2) * (r ^ 2)⁻¹ := by
              simpa only using
                (Finset.sum_mul (s := (Finset.univ : Finset (Fin t × Fin t))) (f :=
                    fun p : Fin t × Fin t => (w p.1 * w p.2) ^ 2) (a := (r ^ 2)⁻¹)).symm
          _ = ((∑ s, (w s) ^ 2) ^ 2) * (r ^ 2)⁻¹ := by
              have hts := tensorSquare_sum_sq (t := t) w
              simp only [hts]
          _ = ∑ s, (w s)^2 := by
              calc
                ((∑ s, (w s)^2) ^ 2) * (r ^ 2)⁻¹
                    = (r ^ 2 * r ^ 2) * (r ^ 2)⁻¹ := by
                        simp only [pow_two, hsq, mul_assoc]
                _ = r ^ 2 := by field_simp [hr2_ne]
                _ = ∑ s, (w s)^2 := by simp only [hsq]
          _ = ∑ s, (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom i s)^2 := by
            simp only [hrhs]

-- Trace of the witness `negWitnessM` (placeholder).
lemma negWitnessM_trace_one
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) = 1 := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  -- Swap the factors in the trace to make row sums appear.
  have htrace_swap :
      Matrix.trace (Vᵀ * V) = Matrix.trace (V * Vᵀ) :=
    Matrix.trace_mul_comm (A := Vᵀ) (B := V)
  -- Compute the trace of `V * Vᵀ` as a double sum of squares.
  have htrace_expanded :
      Matrix.trace (V * Vᵀ) = ∑ p : Fin t × Fin t, ∑ i : n, (V p i)^2 := by
    simp only [trace, transpose, diag_apply, mul_apply, of_apply, pow_two]
  -- Convert the inner sums using the column/row norm lemma.
  have hcol :
      ∑ i : n, ∑ p : Fin t × Fin t, (V p i)^2 =
        ∑ i : n, ∑ s : Fin t,
          (negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s)^2 := by
    refine Finset.sum_congr rfl ?_
    intro i _
    -- `negVcol_norm_sq` turns the row-sum-of-squares of column `i` into the corresponding row
    -- sum in `negEigMatrixScaled`.
    simpa only using (negVcol_norm_sq (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)
  -- Column norms of `negEigMatrixScaled` are `1/t` by orthonormality.
  let Us := negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have horth := negEigMatrixScaled_orthonormal (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hcol_norm (s : Fin t) :
      ∑ i : n, (Us i s)^2 = 1 / (t : ℝ) := by
    -- Take the `s,s` entry of `Usᵀ * Us = (1/t)•I`.
    have h := congrArg (fun M => M s s) horth
    simp only [mul_apply, transpose_apply, one_div, smul_apply, one_apply_eq, smul_eq_mul,
      mul_one] at h
    simpa only [pow_two, one_div] using h
  -- Sum over all columns.
  have hsum_cols :
      ∑ s : Fin t, ∑ i : n, (Us i s)^2 = 1 := by
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt ht
    calc
      ∑ s : Fin t, ∑ i : n, (Us i s)^2
          = ∑ s : Fin t, (1 / (t : ℝ)) := by
              refine Finset.sum_congr rfl ?_ ; intro s _; simpa only [one_div] using hcol_norm s
      _ = (t : ℝ) * (1 / (t : ℝ)) := by
              have htcard : (Fintype.card (Fin t) : ℝ) = t := by simp only [Fintype.card_fin]
              simp only [one_div, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul]
      _ = 1 := by
              field_simp [ht']
  -- Put everything together.
  calc
    Matrix.trace (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
        = Matrix.trace (V * Vᵀ) := by simpa only [negWitnessM] using htrace_swap
    _ = ∑ p : Fin t × Fin t, ∑ i : n, (V p i)^2 := htrace_expanded
    _ = ∑ i : n, ∑ p : Fin t × Fin t, (V p i)^2 := by
          -- swap sums
          classical
          simpa only using (Finset.sum_comm : _)
    _ = ∑ i : n, ∑ s : Fin t, (Us i s)^2 := by
          simpa only [Us] using hcol
    _ = ∑ s : Fin t, ∑ i : n, (Us i s)^2 := by
          classical
          simpa only using (Finset.sum_comm : _)
    _ = 1 := hsum_cols

-- Positivity: `negWitnessM = Vᵀ * V` is PSD.
lemma negWitnessM_posSemidef
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.PosSemidef
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  -- Gram matrices are PSD.
  have hpsd : Matrix.PosSemidef (Matrix.conjTranspose V * V) :=
    Matrix.posSemidef_conjTranspose_mul_self (A := V)
  simpa only [negWitnessM, conjTranspose, RCLike.star_def] using hpsd

-- Symmetry of the witness matrix (Gram matrix of columns of `V`).
lemma negWitnessM_symm
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j =
      negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j i := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  -- Entrywise symmetry of the Gram matrix.
  -- `(Vᵀ * V) i j = ∑ k, V k i * V k j`, which is symmetric by commutativity.
  simp only [negWitnessM, transpose, mul_apply, of_apply, mul_comm]

-- Frobenius bound for `negWitnessM`.
-- Frobenius bound for `negWitnessM` (placeholder).
-- Helper definitions for the Frobenius bound.
section FrobeniusBound

variable {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
  (hBottom : bottomThresholdRank A hHerm μ ≥ t)

-- The eigenvalues corresponding to the selected negative eigenspace.
noncomputable def negEigValues : Fin t → ℝ :=
  fun s => hHerm.eigenvalues
    (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)

noncomputable def UsMatrix : Matrix n (Fin t) ℝ :=
  negEigMatrixScaled (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom

noncomputable def Pproj : Matrix n n ℝ :=
  UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom *
    (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ

-- Frobenius inner product with `Pproj` expressed as a conjugated trace.
lemma frobeniusInner_A_Pproj
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) =
      Matrix.trace
        ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
          A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)) := by
  classical
  let Us := UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom
  have hA_symm : Matrix.transpose A = A := by
    simpa only using hHerm
  have hcycle := Matrix.trace_mul_cycle (A := A) (B := Us) (C := Usᵀ)
  calc
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom)
        = Matrix.trace (Matrix.transpose A * (Us * Usᵀ)) := by
            simp only [Pproj, frobeniusInner_trace, hA_symm, Us]
    _ = Matrix.trace (Usᵀ * A * Us) := by
          have hcyc := Matrix.trace_mul_cycle (A := A) (B := Us) (C := Usᵀ)
          -- hcyc : trace (A*Us*Usᵀ) = trace (Usᵀ*A*Us)
          -- rewrite Aᵀ = A
          simpa only [hA_symm, Matrix.mul_assoc] using hcyc


-- Each selected eigenvalue is ≤ -μ.
lemma negEigValues_le_negμ
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (s : Fin t) :
    negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s ≤ -μ := by
  classical
  -- By construction, `negEigIdx s` is drawn from the subtype `{ i // λᵢ ≤ -μ }`.
  dsimp only [negEigValues, negEigIdx,
    negEigSubtype] at *
      -- The chosen element of the subtype carries the desired property.

  -- The chosen element of the subtype carries the desired property.
  have hcard :
      t ≤ Fintype.card (negEigSubtype (A := A) (n := n) μ hHerm) := by
    simpa only [negEigSubtype, bottomThresholdRank, ge_iff_le] using hBottom
  have hmem :
      hHerm.eigenvalues
          ((Fintype.equivFin (negEigSubtype (A := A) (n := n) μ hHerm)).symm
            (Fin.castLE hcard s)).1 ≤ -μ :=
    ((Fintype.equivFin (negEigSubtype (A := A) (n := n) μ hHerm)).symm
      (Fin.castLE hcard s)).2
  simpa only [ge_iff_le, negEigSubtype] using hmem

-- Sum of the selected eigenvalues is at most `-μ * t`.
lemma sum_negEigValues_le
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    ∑ s, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s ≤ -μ * t := by
  classical
  have hterm : ∀ s : Fin t, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s ≤ -μ :=
    fun s => negEigValues_le_negμ (A := A) (n := n) (μ := μ) hHerm hBottom s
  calc
    ∑ s, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s
        ≤ ∑ s, (-μ) := by
              refine Finset.sum_le_sum (fun s _ => hterm s)
    _ = (Fintype.card (Fin t) : ℝ) * (-μ) := by simp only [Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_neg]
    _ = (-μ) * (t : ℝ) := by
          have ht : (Fintype.card (Fin t) : ℝ) = t := by simp only [Fintype.card_fin]
          simp only [Fintype.card_fin, mul_neg, mul_comm]
    _ = -μ * t := by ring

-- Symmetry of `Pproj`.
lemma Pproj_symm
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j =
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j i := by
  classical
  let Us := UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom
  simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, mul_comm]

-- Action of `A` on the selected eigenvector matrix.
lemma A_mul_negEigMatrix
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ}
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    A * negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom =
      negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom *
        Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom) := by
  classical
  -- Use the spectral decomposition `A = U * diag(λ) * Uᵀ`.
  let U : Matrix n n ℝ := hHerm.eigenvectorUnitary
  have hU_unitary : Uᵀ * U = (1 : Matrix n n ℝ) :=
    (Matrix.mem_unitaryGroup_iff').mp hHerm.eigenvectorUnitary.property
  have hA_decomp :
      A = U * Matrix.diagonal hHerm.eigenvalues * Uᵀ := by
    have hspec := hHerm.spectral_theorem
    -- rewrite `conjTranspose` as `transpose` over ℝ
    simpa only [RCLike.ofReal_real_eq_id, CompTriple.comp_eq, Unitary.conjStarAlgAut_apply] using
      hspec
  -- Derive `A * U = U * diag(λ)`.
  have hAU :
      A * U = U * Matrix.diagonal hHerm.eigenvalues := by
    calc
      A * U = (U * Matrix.diagonal hHerm.eigenvalues * Uᵀ) * U := by
        simp only [hA_decomp, Matrix.mul_assoc]
      _ = U * Matrix.diagonal hHerm.eigenvalues * (Uᵀ * U) := by
        simp only [Matrix.mul_assoc]
      _ = U * Matrix.diagonal hHerm.eigenvalues := by
        simp only [hU_unitary, mul_one]
  -- Evaluate entries columnwise to restrict to the chosen indices.
  ext i s
  -- Left-hand side entry.
  have hL :
      (A * negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) i s =
        (A * U) i (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s) := by
    simp only [mul_apply, negEigMatrix, IsHermitian.eigenvectorUnitary_apply, U]
  -- Right-hand side entry.
  have hR :
      (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom *
          Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom)) i s =
        (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i s) *
          (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s) := by
    simp only [diagonal, negEigValues, mul_apply, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
  -- Use `hAU` to rewrite the left-hand side.
  have hAU_entry :
      (A * U) i (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s) =
        U i (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s) *
          hHerm.eigenvalues (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s) := by
    -- expand `(U * diag λ)` entry
    have := congrArg
      (fun M => M i (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s)) hAU
    simp only [mul_apply, diagonal, of_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte] at this
    simpa only [IsHermitian.eigenvectorUnitary_apply] using this
  -- Assemble.
  calc
    (A * negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) i s
        = (A * U) i (negEigIdx (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom s) := hL
    _ = (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom i s) *
          (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s) := by
          -- unfold `negEigMatrix` and `negEigValues`
          simpa only [negEigMatrix, IsHermitian.eigenvectorUnitary_apply, negEigValues] using
            hAU_entry
    _ = (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom *
      Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom)) i s := hR.symm

-- Conjugating `A` by `UsMatrix` yields a diagonal with the selected eigenvalues scaled by `1/t`.
lemma Us_conjA_diagonal
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
        A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)
      = (1 / (t : ℝ)) • Matrix.diagonal
          (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom) := by
  classical
  let Us := UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom
  -- Express `Us` as a scalar multiple of `negEigMatrix`.
  have hscaled :
      Us = (1 / Real.sqrt (t : ℝ)) •
        negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom := by
    ext i s
    simp only [UsMatrix, negEigMatrixScaled, one_div, smul_apply, smul_eq_mul, Us]
  have hneg := A_mul_negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom
  have hsq :
      (1 / Real.sqrt (t : ℝ)) ^ 2 = 1 / (t : ℝ) := by
    have ht_nonneg : 0 ≤ (t : ℝ) := by exact_mod_cast Nat.zero_le _
    have hroot : (Real.sqrt (t : ℝ)) ^ 2 = (t : ℝ) := Real.sq_sqrt ht_nonneg
    calc
      (1 / Real.sqrt (t : ℝ)) ^ 2 = 1 / (Real.sqrt (t : ℝ)) ^ 2 := by
        ring
      _ = 1 / (t : ℝ) := by simp only [hroot, one_div]
  have hcoef :
      (Real.sqrt (t : ℝ))⁻¹ * (Real.sqrt (t : ℝ))⁻¹ = (t : ℝ)⁻¹ := by
    simpa only [one_div, pow_two] using hsq
  -- Compute `Usᵀ * A * Us` by pulling out the scalars.
  calc
      Usᵀ * A * Us
          = (((1 / Real.sqrt (t : ℝ)) •
              (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)))ᵀ *
            A *
            (((1 / Real.sqrt (t : ℝ)) •
              (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom))) := by
            simp only [hscaled, one_div, transpose_smul, smul_mul, Matrix.mul_smul]
    _ = (1 / (t : ℝ)) •
          (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
            (A *
              (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)) := by
            simp only [one_div, transpose_smul, smul_mul, Matrix.mul_smul, Matrix.mul_assoc,
              smul_smul, hcoef]
    _ = (1 / (t : ℝ)) •
          (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom)ᵀ *
            (negEigMatrix (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom) *
              Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom) := by
            simp only [one_div, hneg, smul_mul, Algebra.smul_mul_assoc, Matrix.mul_assoc]
    _ = (1 / (t : ℝ)) •
          (1 : Matrix (Fin t) (Fin t) ℝ) *
            Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom) := by
            -- orthonormal columns
            simp only [one_div, smul_mul,
              negEigMatrix_cols_orthonormal (A := A) (n := n) (μ := μ) (t := t) hHerm hBottom,
              Algebra.smul_mul_assoc, one_mul]
    _ = (1 / (t : ℝ)) • Matrix.diagonal
      (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom) := by
            simp only [one_div, Algebra.smul_mul_assoc, one_mul]

-- Trace of the conjugated matrix `Usᵀ * A * Us`.
lemma trace_Us_conjA
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace
      ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
          A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom))
        = (1 / (t : ℝ)) * ∑ s, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s := by
  classical
  have hdiag :=
    Us_conjA_diagonal (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have htrace := congrArg Matrix.trace hdiag
  -- Pull out the scalar and use the diagonal trace.
  have htrace' :
      Matrix.trace
          ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
              A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)) =
        (1 / (t : ℝ)) * Matrix.trace
          (Matrix.diagonal (negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom)) := by
    simpa only [one_div, trace_diagonal, trace_smul, smul_eq_mul] using htrace
  -- Finish by evaluating the trace of a diagonal matrix.
  simpa only [one_div, trace_diagonal] using htrace'

-- The trace of `Usᵀ * A * Us` is at most `-μ`.
lemma trace_Us_conjA_le
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace
      ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
          A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom))
        ≤ -μ := by
  classical
  have htrace := trace_Us_conjA (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hsum := sum_negEigValues_le (A := A) (n := n) (μ := μ) hHerm (t := t) hBottom
  have ht_ne : (t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  have hnonneg : 0 ≤ (1 / (t : ℝ)) := by positivity
  have hmult := mul_le_mul_of_nonneg_left hsum hnonneg
  have hfinal : (1 / (t : ℝ)) * (-μ * t) = -μ := by
    field_simp [ht_ne]
  calc
    Matrix.trace ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
        A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom))
        = (1 / (t : ℝ)) * ∑ s, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s := by
            exact htrace
    _ ≤ (1 / (t : ℝ)) * (-μ * t) := hmult
    _ = -μ := hfinal

-- Exact value of `frobeniusInner A Pproj` in terms of the selected eigenvalues.
lemma frobeniusInner_A_Pproj_eq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) =
      (1 / (t : ℝ)) * ∑ s, negEigValues (A := A) (n := n) (μ := μ) hHerm hBottom s := by
  classical
  -- From `frobeniusInner_A_Pproj` and `trace_Us_conjA`.
  have htrace :=
    trace_Us_conjA (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hinner :=
    frobeniusInner_A_Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom
  simpa only [hinner, one_div] using htrace

-- Convert the trace bound into a Frobenius-inner-product bound with `Pproj`.
lemma frobeniusInner_A_Pproj_le
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) ≤ -μ := by
  classical
  have htrace :=
    trace_Us_conjA_le (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hinner :=
    frobeniusInner_A_Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom
  -- Combine the two equalities/inequalities.
  calc
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom)
        = Matrix.trace
            ((UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)ᵀ *
          A * (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom)) := hinner
    _ ≤ -μ := htrace

-- Convenience: `frobeniusInner A Pproj` is nonpositive.
lemma frobeniusInner_A_Pproj_nonpos
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (hμ : 0 ≤ μ) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) ≤ 0 := by
  have h := frobeniusInner_A_Pproj_le (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hneg : -μ ≤ 0 := by linarith
  exact le_trans h hneg

-- Consequently, the square of `frobeniusInner A Pproj` is at least `μ^2`.
lemma frobeniusInner_A_Pproj_sq_ge
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (hμ : 0 ≤ μ) :
    (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom)) ^ 2 ≥ μ ^ 2 := by
  -- Shorthand for the inner product value.
  set x : ℝ := frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom)
  have hx_le : x ≤ -μ :=
    frobeniusInner_A_Pproj_le (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hx_nonpos : x ≤ 0 := by linarith
  have hx_nonneg : 0 ≤ -x := by linarith
  -- Compare absolute values, then square.
  have hμ_abs : |μ| = μ := abs_of_nonneg hμ
  have hx_abs : |-x| = -x := abs_of_nonneg hx_nonneg
  have hμ_le_negx : μ ≤ -x := by linarith
  have habs : |μ| ≤ |-x| := by simpa only [hμ_abs, hx_abs] using hμ_le_negx
  have hsq : μ ^ 2 ≤ (-x) ^ 2 := by
    have := sq_le_sq.mpr habs
    simpa only [pow_two, mul_neg, neg_mul, neg_neg, ge_iff_le] using this
  have hx_sq : (-x) ^ 2 = x ^ 2 := by ring
  have hres : μ ^ 2 ≤ x ^ 2 := by simpa only [hx_sq] using hsq
  simpa only [ge_iff_le] using hres

-- Trace of `A * negWitnessM` reduced to diagonals of `Pproj` (using symmetry).
-- Tensor-square identity specialized to rows of `Us`.
lemma sum_tensorRow_sq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    ∑ p : Fin t × Fin t,
      (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i p.1 *
        UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i p.2) ^ 2
      = (∑ s, (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s) ^ 2) ^ 2 := by
  classical
  simpa only using
    (tensorSquare_sum_sq (t := t) (u := fun s =>
      UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s))

-- Cauchy–Schwarz on the rows of `UsMatrix`: `(Pproj i j)^2 ≤ Pproj i i * Pproj j j`.
lemma Pproj_entry_sq_le_diag
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j)^2 ≤
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := by
  classical
  -- Shorthand for `Us`.
  let Us := UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom
  -- Identify the relevant entries as sums of products.
  have hdot :
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = ∑ s, Us i s * Us j s := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, Us]
  have hdiag_i :
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = ∑ s, (Us i s)^2 := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, pow_two, Us]
  have hdiag_j :
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = ∑ s, (Us j s)^2 := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, pow_two, Us]
  -- Cauchy–Schwarz on the finite sum.
  have hcs :
      (∑ s, Us i s * Us j s) ^ 2 ≤ (∑ s, (Us i s) ^ 2) * (∑ s, (Us j s) ^ 2) := by
    simpa only [pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun s => Us i s) (g := fun s =>
        Us j s))
  -- Reassemble.
  simpa only [hdot, hdiag_i, hdiag_j, ge_iff_le] using hcs

-- Diagonal entries of `Pproj` are nonnegative (sums of squares).
lemma Pproj_diag_nonneg
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    0 ≤ Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
  classical
  let Us := UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom
  have hdiag :
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = ∑ s, (Us i s)^2 := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, pow_two, Us]
  have hnonneg : 0 ≤ ∑ s, (Us i s)^2 := by positivity
  simpa only [hdiag, ge_iff_le] using hnonneg

-- Explicit diagonal formula for later rewrites.
lemma Pproj_diag_eq_sum_sq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i =
      ∑ s, (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s)^2 := by
  classical
  simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, pow_two]

-- Column norm of `negVcol` matches the corresponding diagonal of `Pproj`.
lemma negVcol_norm_sq_Pdiag
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    ∑ p, (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 =
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
  classical
  -- Use the existing norm identity and rewrite via `Pproj_diag_eq_sum_sq`.
  have h := negVcol_norm_sq (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hdiag := Pproj_diag_eq_sum_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  -- The RHS of `h` is the sum of squares of the `UsMatrix` row.
  simpa only using h.trans hdiag.symm

-- Diagonal entries of `negWitnessM` coincide with the corresponding diagonal of `Pproj`.
lemma negWitnessM_diag_eq_Pproj
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i i =
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
  classical
  -- Expand the `(i,i)` entry of `Vᵀ * V` as the squared norm of column `i`.
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i i =
        ∑ p, (negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i)^2 := by
    -- `(Vᵀ*V) i i = ∑ p, V p i * V p i`.
    simp only [negWitnessM, transpose, negVmatrix, mul_apply, of_apply, pow_two]
  -- Replace with the projection diagonal.
  simpa only [hsum] using
    (negVcol_norm_sq_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)

-- Each entry of `Vᵀ * V` is bounded by the product of the corresponding diagonals of `Pproj`.
lemma negWitnessM_entry_sq_le
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 ≤
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := by
  classical
  -- Columns of `V`.
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j
        = ∑ p, V p i * V p j := by
    simp only [negWitnessM, transpose, mul_apply, of_apply, V]
  -- Cauchy–Schwarz on the finite sum over columns.
  have hcs :
      (∑ p, V p i * V p j) ^ 2 ≤ (∑ p, (V p i) ^ 2) * (∑ p, (V p j) ^ 2) := by
    simpa only [pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (s := Finset.univ) (f := fun p => V p i) (g := fun p =>
        V p j))
  -- Rewrite the column norms via `Pproj`.
  have hnorm_i :
      ∑ p, (V p i) ^ 2 = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
    simpa only using negVcol_norm_sq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  have hnorm_j :
      ∑ p, (V p j) ^ 2 = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j := by
    simpa only using negVcol_norm_sq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom j
  -- Assemble the inequality.
  have hcs' :
      ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j) ^ 2 ≤
        (∑ p, (V p i) ^ 2) * (∑ p, (V p j) ^ 2) := by
    have := hcs
    -- replace the entry with the sum expression
    simpa only [hsum, ge_iff_le] using this
  simpa only [ge_iff_le, hnorm_i, hnorm_j] using hcs'

-- If a diagonal of `Pproj` is zero, the corresponding row/column of `Pproj` vanishes.
lemma Pproj_diag_zero_row_col_zero
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n)
    (hdiag : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0) :
    ∀ j, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
  classical
  -- From the diagonal formula, all entries in the row of `UsMatrix` vanish.
  have hdiag_sum := Pproj_diag_eq_sum_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  have hsum_zero :
      ∑ s, (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s)^2 = 0 := by
    simpa only [hdiag_sum] using congrArg (fun x => x) hdiag
  have hzero_entries :
      ∀ s, UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s = 0 := by
    intro s
    have hs_nonneg : ∀ s, 0 ≤ (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s)^2 :=
      fun _ => sq_nonneg _
    have hsum_eq :=
      (Finset.sum_eq_zero_iff_of_nonneg (by intro s _; exact hs_nonneg s)).1 hsum_zero
    have : (UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s)^2 = 0 :=
      hsum_eq s (by simp only [Finset.mem_univ])
    exact sq_eq_zero_iff.mp this
  intro j
  have hdot :
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j =
        ∑ s, UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s *
          UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom j s := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply]
  -- Every term in the sum is zero.
  have hdot_zero :
      ∑ s, UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom i s *
          UsMatrix (A := A) (n := n) (μ := μ) hHerm ht hBottom j s = 0 := by
    simp only [hzero_entries, zero_mul, Finset.sum_const_zero]
  simp only [hdot, hdot_zero]

-- If a diagonal of `Pproj` is zero, the corresponding column of `V` vanishes.
lemma negVcol_zero_of_Pdiag_zero
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i : n}
    (hdiag : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0) :
    ∀ p, negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p = 0 := by
  classical
  have hnorm := negVcol_norm_sq_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hsum_zero :
      ∑ p, (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 = 0 := by
    simpa only [hdiag] using congrArg (fun x => x) hnorm
  have hs_nonneg :
      ∀ p, 0 ≤ (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 :=
    fun _ => sq_nonneg _
  have hsum_eq :=
    Finset.sum_eq_zero_iff_of_nonneg (by intro p _; exact hs_nonneg p) |>.1 hsum_zero
  intro p
  have : (negVcol (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i p)^2 = 0 :=
    hsum_eq p (by simp only [Finset.mem_univ])
  exact sq_eq_zero_iff.mp this

-- Convenience wrappers: if a diagonal entry of `Pproj` vanishes, the whole row/column vanishes.
@[simp]
lemma Pproj_entry_zero_left
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hdi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
  have hrow := Pproj_diag_zero_row_col_zero (A := A) (n := n) (μ := μ) hHerm ht hBottom i hdi j
  simpa only using hrow

@[simp]
lemma Pproj_entry_zero_right
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hdj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
  have hcol := Pproj_diag_zero_row_col_zero (A := A) (n := n) (μ := μ) hHerm ht hBottom j hdj i
  have hsymm := Pproj_symm (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
  -- Convert `P j i = 0` to `P i j = 0` using symmetry.
  simpa only [hsymm] using hcol

-- If both diagonals vanish, the corresponding entry of `negWitnessM` is zero.
lemma negWitnessM_entry_zero_of_diag_zero
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hdi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0)
    (hdj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j = 0 := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hVi_zero : ∀ p, V p i = 0 := by
    intro p
    have h := negVcol_zero_of_Pdiag_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdi p
    simpa only using h
  have hVj_zero : ∀ p, V p j = 0 := by
    intro p
    have h := negVcol_zero_of_Pdiag_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdj p
    simpa only using h
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j
        = ∑ p, V p i * V p j := by
    simp only [negWitnessM, transpose, mul_apply, of_apply, V]
  have hzero_sum : ∑ p, V p i * V p j = 0 := by
    have hzero : ∀ p, V p i * V p j = 0 := by
      intro p
      have h1 := hVi_zero p
      have h2 := hVj_zero p
      simp only [h1, h2, mul_zero]
    simp only [hzero, Finset.sum_const_zero]
  simp only [hsum, hzero_sum]

-- Stronger entrywise bound: each square of an entry of `negWitnessM` is bounded by
-- the square of the corresponding entry of `Pproj`.
lemma negWitnessM_entry_sq_le_Pproj_sq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 ≤
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j)^2 := by
  classical
  -- Shorthands.
  let P := Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom
  let wᵢ : Fin t → ℝ :=
    negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  let wⱼ : Fin t → ℝ :=
    negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
  let rᵢ : ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  let rⱼ : ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j

  have hdiag_nonneg_i := Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  have hdiag_nonneg_j := Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom j

  -- Case split: zero diagonals force zero rows/columns.
  by_cases hdi : P i i = 0
  · have hrow_zero := Pproj_diag_zero_row_col_zero
      (A := A) (n := n) (μ := μ) hHerm ht hBottom i hdi j
    have hVcol_zero :
        ∀ p, negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i = 0 := by
      intro p
      have h := negVcol_zero_of_Pdiag_zero
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdi p
      simpa only [negVmatrix] using h
    have hMij_zero :
        (negWitnessM (A := A) (n := n) (μ := μ) (t := t)
          hHerm ht hBottom) i j = 0 := by
      classical
      simp only [negWitnessM, transpose, mul_apply, of_apply, hVcol_zero, zero_mul,
        Finset.sum_const_zero]
    have hPij_zero : P i j = 0 := by simpa only using hrow_zero
    have hleft : ((negWitnessM (A := A) (n := n) (μ := μ) (t := t)
      hHerm ht hBottom) i j)^2 = 0 := by
      simp only [hMij_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    have hright : (P i j)^2 = 0 := by simp only [hPij_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    linarith
  -- Symmetric case: `P j j = 0`.
  · by_cases hdj : P j j = 0
    · have hVcol_zero :
          ∀ p, negVmatrix (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom p j = 0 := by
        intro p
        have h := negVcol_zero_of_Pdiag_zero (A := A) (n := n) (μ := μ) (t := t)
          hHerm ht hBottom hdj p
        simpa only [negVmatrix] using h
      have hMij_zero :
          (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j = 0 := by
        classical
        simp only [negWitnessM, transpose, mul_apply, of_apply, hVcol_zero, mul_zero,
          Finset.sum_const_zero]
      have hleft : ((negWitnessM (A := A) (n := n) (μ := μ) (t := t)
        hHerm ht hBottom) i j)^2 = 0 := by
        simp only [hMij_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      have htarget :
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom) i j)^2 ≤ (P i j)^2 := by
        have hnonneg : 0 ≤ (P i j)^2 := sq_nonneg _
        nlinarith
      simpa only [ge_iff_le] using htarget
    -- Main case: positive diagonals.
    · have hPii_pos : 0 < P i i := lt_of_le_of_ne hdiag_nonneg_i (ne_comm.mp hdi)
      have hPjj_pos : 0 < P j j := lt_of_le_of_ne hdiag_nonneg_j (ne_comm.mp hdj)

      -- rᵢ^2 = Pᵢᵢ and rⱼ^2 = Pⱼⱼ.
      have hri_sq : rᵢ ^ 2 = P i i := by
        -- unfold and use the explicit diagonal expression.
        have hnonneg : 0 ≤ ∑ s, (wᵢ s)^2 := by positivity
        calc
          rᵢ ^ 2 = ∑ s, (wᵢ s)^2 := by
            dsimp only [negRowNorm, rᵢ]
            simpa only [pow_two] using (Real.sq_sqrt hnonneg)
          _ = P i i := by
            -- rewrite via `Pproj_diag_eq_sum_sq`
            have hdiag :=
              Pproj_diag_eq_sum_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom i
            simpa only [negRow, UsMatrix, wᵢ, P] using hdiag.symm
      have hrj_sq : rⱼ ^ 2 = P j j := by
        have hnonneg : 0 ≤ ∑ s, (wⱼ s)^2 := by positivity
        calc
          rⱼ ^ 2 = ∑ s, (wⱼ s)^2 := by
            dsimp only [negRowNorm, rⱼ]
            simpa only [pow_two] using (Real.sq_sqrt hnonneg)
          _ = P j j := by
            have hdiag :=
              Pproj_diag_eq_sum_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom j
            simpa only [negRow, UsMatrix, wⱼ, P] using hdiag.symm

      have hri_ne : rᵢ ≠ 0 := by
        intro hzero
        have hcontr : P i i = 0 := by nlinarith [hri_sq, hzero]
        exact hdi hcontr
      have hrj_ne : rⱼ ≠ 0 := by
        intro hzero
        have hcontr : P j j = 0 := by nlinarith [hrj_sq, hzero]
        exact hdj hcontr

      -- Expand the entry of `negWitnessM` in terms of the rows wᵢ, wⱼ.
      have hentry :
          (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
            ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
              (∑ s, wᵢ s * wⱼ s) ^ 2 := by
        classical
        -- First expand `negWitnessM` as the double sum.
        have hsum :
            (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
              ∑ p : Fin t × Fin t,
                negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j := by
          simp only [negWitnessM, transpose, mul_apply, of_apply]
        -- Rewrite the sum using the nonzero norms and pull out constants.
        have hrewrite :
            ∑ p : Fin t × Fin t,
                negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j
              = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                  ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := by
          -- pull out the constant via `mul_sum`
          have hconst :
              ∑ p : Fin t × Fin t,
                  ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                    ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) =
                ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                  ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := by
            have h :=
              Finset.mul_sum
                (a := ((rᵢ)⁻¹ * (rⱼ)⁻¹))
                (s := (Finset.univ : Finset (Fin t × Fin t)))
                (f := fun p : Fin t × Fin t =>
                  (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2))
            simpa only [mul_assoc, mul_comm] using h.symm
          -- identify each term of the sum
          have hterm :
              ∀ p : Fin t × Fin t,
                negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j =
                    ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                      ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) := by
            intro p
            rcases p with ⟨p1, p2⟩
            have hmain :
                negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ i *
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ j =
                  ((wᵢ p1 * wᵢ p2) * (rᵢ)⁻¹) * ((wⱼ p1 * wⱼ p2) * (rⱼ)⁻¹) := by
              simp only [negVmatrix, negVcol, hri_ne, ↓reduceDIte, div_eq_mul_inv, hrj_ne, wᵢ, rᵢ,
                wⱼ, rⱼ]
            calc
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ i *
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ j
                  = ((wᵢ p1 * wᵢ p2) * (rᵢ)⁻¹) * ((wⱼ p1 * wⱼ p2) * (rⱼ)⁻¹) := hmain
              _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) * ((wᵢ p1 * wᵢ p2) * (wⱼ p1 * wⱼ p2)) := by
                simp only [mul_assoc, mul_left_comm, mul_comm]
          calc
            ∑ p, negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
                negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j
                = ∑ p : Fin t × Fin t, ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                    ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) := by
              refine Finset.sum_congr rfl ?_ ; intro p hp; simpa only using hterm p
            _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                  ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := hconst
        -- Recognize the tensor-square sum.
        have htensor :
            ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) =
              (∑ s, wᵢ s * wⱼ s) ^ 2 := by
          simpa only using tensorSquare_sum_mul (t := t) wᵢ wⱼ
        -- Chain the equalities together.
        calc
          (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j
              = ∑ p : Fin t × Fin t,
                  negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
                    negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j := hsum
          _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := hrewrite
          _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) * (∑ s, wᵢ s * wⱼ s) ^ 2 := by
                simp only [htensor]

      -- Express the correlation ∑ wᵢ wⱼ as the entry P i j.
      have hPij :
          P i j = ∑ s, wᵢ s * wⱼ s := by
        simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, negRow, P, wᵢ, wⱼ]

      have hentry_sq :
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 =
            (P i j) ^ 4 / (P i i * P j j) := by
        have hentry' := hentry
        calc
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2
              = (((rᵢ)⁻¹ * (rⱼ)⁻¹) * (P i j) ^ 2)^2 := by simp only [hentry', hPij]
          _ = (P i j) ^ 4 * (((rᵢ)⁻¹ * (rⱼ)⁻¹) ^ 2) := by ring
          _ = (P i j) ^ 4 * ((rᵢ ^ 2)⁻¹ * (rⱼ ^ 2)⁻¹) := by ring
          _ = (P i j) ^ 4 * ((P i i)⁻¹ * (P j j)⁻¹) := by
                simp only [hri_sq, hrj_sq]
          _ = (P i j) ^ 4 / (P i i * P j j) := by
                simp only [mul_left_comm, div_eq_mul_inv, _root_.mul_inv_rev, mul_comm]

      -- Use `(P i j)^2 ≤ P i i * P j j` to bound the ratio by 1.
      have hPij_sq_le := Pproj_entry_sq_le_diag (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
      have hpos_denom : 0 < P i i * P j j := mul_pos hPii_pos hPjj_pos
      have hratio : (P i j) ^ 2 / (P i i * P j j) ≤ 1 := by
        have hdiv :
            (P i j) ^ 2 / (P i i * P j j) ≤
              (P i i * P j j) / (P i i * P j j) :=
          div_le_div_of_nonneg_right hPij_sq_le (le_of_lt hpos_denom)
        have hne : (P i i * P j j) ≠ 0 := by
          have hi : (P i i) ≠ 0 := ne_of_gt hPii_pos
          have hj : (P j j) ≠ 0 := ne_of_gt hPjj_pos
          nlinarith
        have hunit : (P i i * P j j) / (P i i * P j j) = (1 : ℝ) := by
          field_simp [hne]
        linarith [hdiv, hunit]

      have hnonneg_num : 0 ≤ (P i j) ^ 2 := sq_nonneg _
      have hbound :
          (P i j) ^ 4 / (P i i * P j j) ≤ (P i j) ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left hratio hnonneg_num
        have hrewrite :
            (P i j) ^ 4 / (P i i * P j j) =
              (P i j) ^ 2 * ((P i j) ^ 2 / (P i i * P j j)) := by
          ring_nf
        simpa only [hrewrite, ge_iff_le, mul_one] using hmul

      -- Final inequality.
      have htarget :
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom) i j)^2 ≤ (P i j) ^ 2 := by
        calc
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom) i j)^2
              = (P i j) ^ 4 / (P i i * P j j) := hentry_sq
          _ ≤ (P i j) ^ 2 := hbound
      have htarget' :
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 ≤
            (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 := by
        simpa only using htarget
      exact htarget'

-- Row norm squared matches the corresponding diagonal of `Pproj`.
lemma negRowNorm_nonneg
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    0 ≤ negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i := by
  classical
  unfold negRowNorm
  exact Real.sqrt_nonneg _

lemma negRowNorm_sq_eq_Pdiag
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)^2 =
      Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
  classical
  let w : Fin t → ℝ := negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hnonneg : 0 ≤ ∑ s, (w s)^2 := by positivity
  have hnorm :
      (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)^2 =
        ∑ s, (w s)^2 := by
    dsimp only [negRow, negRowNorm, w] at *
    simpa only [pow_two] using (Real.sq_sqrt hnonneg)
  have hdiag :=
    Pproj_diag_eq_sum_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  simpa only using hnorm.trans hdiag.symm

-- Relate the row norm to the diagonal of `Pproj`.
lemma negRowNorm_eq_sqrt_Pdiag
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i : n) :
    negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i =
      Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) := by
  classical
  have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  have hnorm_nonneg :
      0 ≤ negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i :=
    negRowNorm_nonneg (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hP_nonneg :
      0 ≤ Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i :=
    Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  calc
    negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
        = |negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i| := by
            simp only [abs_of_nonneg hnorm_nonneg]
    _ = Real.sqrt ((negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)^2) := by
            simp only [Real.sqrt_sq_eq_abs]
    _ = Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) := by
            simp only [hsq]

-- If the row norm vanishes, the corresponding row of `Pproj` vanishes.
lemma negRowNorm_zero_row_zero
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hr : negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i = 0) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
  have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
  have hdiag : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0 := by
    have hr_sq : (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i)^2 = 0 := by
      nlinarith [hr]
    linarith
  exact Pproj_entry_zero_left (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdiag

-- If the row norm vanishes, the corresponding row of `Pproj` vanishes.

-- Exact entry formula when both relevant diagonals of `Pproj` are positive.
lemma negWitnessM_entry_pos_diag
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n)
    (hPii_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i)
    (hPjj_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
        (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i *
          negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j) := by
  classical
  -- Shorthands.
  let P := Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom
  let wᵢ : Fin t → ℝ := negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  let wⱼ : Fin t → ℝ := negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
  let rᵢ : ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  let rⱼ : ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j

  have hri_sq : rᵢ ^ 2 = P i i :=
    negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hrj_sq : rⱼ ^ 2 = P j j :=
    negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j

  have hri_ne : rᵢ ≠ 0 := by nlinarith
  have hrj_ne : rⱼ ≠ 0 := by nlinarith

  -- Expand the `(i,j)` entry of `Vᵀ * V` and factor the constants.
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
        ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
          (∑ s, wᵢ s * wⱼ s) ^ 2 := by
    have hsum_raw :
        (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
          ∑ p : Fin t × Fin t,
            negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j := by
      classical
      simp only [negWitnessM, transpose, mul_apply, of_apply]
    have hrewrite :
        ∑ p : Fin t × Fin t,
            negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j
          = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
              ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := by
      -- Pull out the constants using `mul_sum`.
      have hconst :
          ∑ p : Fin t × Fin t,
              ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) =
            ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
              ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := by
        have h :=
          Finset.mul_sum
            (a := ((rᵢ)⁻¹ * (rⱼ)⁻¹))
            (s := (Finset.univ : Finset (Fin t × Fin t)))
            (f := fun p : Fin t × Fin t =>
              (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2))
        simpa only [mul_assoc, mul_comm] using h.symm
      -- Identify each term.
      have hterm :
          ∀ p : Fin t × Fin t,
            negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j =
                ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                  ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) := by
        intro p
        rcases p with ⟨p1, p2⟩
        -- unfold once and use the nonzero norms to drop the conditional branches
        have hmain :
            negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ i *
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ j =
              ((wᵢ p1 * wᵢ p2) * (rᵢ)⁻¹) * ((wⱼ p1 * wⱼ p2) * (rⱼ)⁻¹) := by
          simp only [negVmatrix, negVcol, hri_ne, ↓reduceDIte, div_eq_mul_inv, hrj_ne, wᵢ, rᵢ, wⱼ,
            rⱼ]
        calc
          negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ i *
              negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom ⟨p1, p2⟩ j
              = ((wᵢ p1 * wᵢ p2) * (rᵢ)⁻¹) * ((wⱼ p1 * wⱼ p2) * (rⱼ)⁻¹) := hmain
          _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) * ((wᵢ p1 * wᵢ p2) * (wⱼ p1 * wⱼ p2)) := by
            simp only [mul_assoc, mul_left_comm, mul_comm]
      calc
        ∑ p, negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p i *
            negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom p j
            = ∑ p : Fin t × Fin t, ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
                ((wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2)) := by
                  refine Finset.sum_congr rfl ?_ ; intro p hp; simpa only using hterm p
        _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
              ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := hconst
    have htensor :
        ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) =
          (∑ s, wᵢ s * wⱼ s) ^ 2 := by
      simpa only using tensorSquare_sum_mul (t := t) wᵢ wⱼ
    calc
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j = _ := hsum_raw
      _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) *
            ∑ p : Fin t × Fin t, (wᵢ p.1 * wᵢ p.2) * (wⱼ p.1 * wⱼ p.2) := hrewrite
      _ = ((rᵢ)⁻¹ * (rⱼ)⁻¹) * (∑ s, wᵢ s * wⱼ s) ^ 2 := by simp only [htensor]

  -- The correlation term is exactly `P i j`.
  have hPij :
      P i j = ∑ s, wᵢ s * wⱼ s := by
    simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, negRow, P, wᵢ, wⱼ]

  -- Substitute and rewrite the scalar prefactor.
  have hentry :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
        ((rᵢ)⁻¹ * (rⱼ)⁻¹) * (P i j) ^ 2 := by
    simpa only [hPij] using hsum

  have hmul :
      ((rᵢ)⁻¹ * (rⱼ)⁻¹) * (P i j) ^ 2 =
        (P i j) ^ 2 / (rᵢ * rⱼ) := by
    simp only [mul_comm, div_eq_mul_inv, _root_.mul_inv_rev]

  simpa only [hmul] using hentry

-- If a diagonal is zero, the corresponding entry of `negWitnessM` vanishes (left index).
@[simp]
lemma negWitnessM_entry_zero_left
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hdi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j = 0 := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hVcol_zero : ∀ p, V p i = 0 := by
    intro p
    have h :=
      negVcol_zero_of_Pdiag_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdi p
    simpa only using h
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
        ∑ p, V p i * V p j := by
    simp only [negWitnessM, transpose, mul_apply, of_apply, V]
  have hzero_sum : ∑ p, V p i * V p j = 0 := by
    have hterm : ∀ p, V p i * V p j = 0 := by
      intro p; simp only [hVcol_zero p, zero_mul]
    simp only [hterm, Finset.sum_const_zero]
  simp only [hsum, hzero_sum]

-- If a diagonal is zero, the corresponding entry of `negWitnessM` vanishes (right index).
@[simp]
lemma negWitnessM_entry_zero_right
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hdj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j = 0 := by
  classical
  let V := negVmatrix (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  have hVcol_zero : ∀ p, V p j = 0 := by
    intro p
    have h :=
      negVcol_zero_of_Pdiag_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hdj p
    simpa only using h
  have hsum :
      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
        ∑ p, V p i * V p j := by
    simp only [negWitnessM, transpose, mul_apply, of_apply, V]
  have hzero_sum : ∑ p, V p i * V p j = 0 := by
    have hterm : ∀ p, V p i * V p j = 0 := by
      intro p; simp only [hVcol_zero p, mul_zero]
    simp only [hterm, Finset.sum_const_zero]
  simp only [hsum, hzero_sum]

-- A cleaner formula for the `(i,j)` entry when both diagonals are positive.
lemma negWitnessM_entry_pos_diag_sqrt
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n)
    (hPii_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i)
    (hPjj_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
      (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
      (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
        Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)) := by
  classical
  -- Start from the formula with row norms.
  have hentry :=
    negWitnessM_entry_pos_diag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
      hPii_pos hPjj_pos
  -- Replace the norms by square roots of diagonals.
  have hri :=
    negRowNorm_eq_sqrt_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hrj :=
    negRowNorm_eq_sqrt_Pdiag (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
  -- Rewrite the denominator.
  have hden :
      (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i) *
        (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j) =
          Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
            Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := by
    simp only [hri, hrj]
  -- Finish.
  simpa only [hden] using hentry

-- Uniform entry formula: if a diagonal of `Pproj` vanishes, the entry is zero;
-- otherwise it has the closed form with square roots of diagonals.
lemma negWitnessM_entry_formula
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
      if _ : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0 then 0
      else if _ : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0 then 0
      else
        (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
          (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
            Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)) := by
  classical
  by_cases hPi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0
  · -- Left diagonal zero.
    have hzero :=
      negWitnessM_entry_zero_left
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hPi (i := i) (j := j)
    simp only [hPi, negWitnessM_entry_zero_left, ↓reduceDIte]
  · by_cases hPj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0
    · -- Right diagonal zero.
      have hzero :=
        negWitnessM_entry_zero_right
          (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hPj (i := i) (j := j)
      simp only [hPj, negWitnessM_entry_zero_right, hPi, ↓reduceDIte]
    · -- Both diagonals positive (since they are nonnegative and nonzero).
      have hdiag_nonneg_i :=
        Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom i
      have hdiag_nonneg_j :=
        Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom j
      have hPii_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i :=
        lt_of_le_of_ne hdiag_nonneg_i (Ne.symm hPi)
      have hPjj_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j :=
        lt_of_le_of_ne hdiag_nonneg_j (Ne.symm hPj)
      have hpos :=
        negWitnessM_entry_pos_diag_sqrt (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
          hPii_pos hPjj_pos
      have hfinal : (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j =
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
            (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
              Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)) := hpos
      -- Avoid expensive reduction; reuse the computed equality.
      simp only [hfinal, hPi, ↓reduceDIte, hPj]

-- Entries of `negWitnessM` are nonnegative (useful when paired with entrywise-nonnegative `A`).
lemma negWitnessM_entry_nonneg
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    0 ≤ negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j := by
  classical
  -- Expand using the explicit entry formula.
  have h := negWitnessM_entry_formula (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
  -- Case split on the diagonals of `Pproj`.
  by_cases hPi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0
  · simp only [hPi, negWitnessM_entry_zero_left, le_refl]
  · -- now `Pproj ii ≠ 0`
    by_cases hPj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0
    · simp only [hPj, negWitnessM_entry_zero_right, le_refl]
    · have hdiag_nonneg_i :=
        Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom i
      have hdiag_nonneg_j :=
        Pproj_diag_nonneg (A := A) (n := n) (μ := μ) hHerm ht hBottom j
      have hPi_pos :
          0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i :=
        lt_of_le_of_ne hdiag_nonneg_i (by intro h; exact hPi h.symm)
      have hPj_pos :
          0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j :=
        lt_of_le_of_ne hdiag_nonneg_j (by intro h; exact hPj h.symm)
      have hsqrt_i :
          0 < Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) :=
        Real.sqrt_pos.mpr hPi_pos
      have hsqrt_j :
          0 < Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) :=
        Real.sqrt_pos.mpr hPj_pos
      have hden_pos : 0 <
          Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
            Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) :=
        mul_pos hsqrt_i hsqrt_j
      -- The numerator is a square, so nonnegative; divide by positive denominator.
      have hnum_nonneg :
          0 ≤ (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 :=
        sq_nonneg _
      have hentry_nonneg :
          0 ≤ (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
              (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
                Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)) := by
        exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
      have hrewrite :
          negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j =
            (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
              (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
                Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)) := by
        simp only [h, hPi, ↓reduceDIte, hPj]
      have hpos_entry :
          0 ≤ (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j := by
        simpa only [hrewrite] using hentry_nonneg
      exact hpos_entry

-- A plain finite Cauchy–Schwarz inequality for real-valued functions on a finite type.
lemma cauchy_schwarz_sum_square {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ) :
    (∑ i, f i * g i)^2 ≤ (∑ i, (f i)^2) * (∑ i, (g i)^2) := by
  classical
  simpa only [pow_two] using
    (Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset ι)) (f := f) (g := g))

-- A weighted Cauchy–Schwarz on `A` and the rows of `UsMatrix`, tailored to Lemma 4.4 Condition 1.

-- Translate `frobeniusInner` into a double sum over `A` and the explicit entries of `Pproj`.
lemma frobeniusInner_A_Pproj_explicit
    (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) =
      ∑ i, ∑ j, A i j * Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j := by
  rfl

-- Expand the Pproj entries in terms of the rows `w_i`.
lemma Pproj_entry_as_row_inner
    (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j =
      ∑ s, negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s := by
  classical
  simp only [Pproj, UsMatrix, transpose, mul_apply, of_apply, negRow]

-- If a row norm is zero, the corresponding row correlation with any other row vanishes.
lemma negRow_inner_zero_left
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hr : negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i = 0) :
    ∑ s,
      negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s = 0 := by
  have hP :=
    negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hr (j := j)
  have hinner :=
    Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
  simpa only [hinner] using hP

lemma negRow_inner_zero_right
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) {i j : n}
    (hr : negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j = 0) :
    ∑ s,
      negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s = 0 := by
  have hP :=
    negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hr (j := i)
  have hinner :=
    Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
  have hsymm := Pproj_symm (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
  have hzero : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
    simpa only [hsymm] using hP
  simpa only [hinner] using hzero

-- Mixed sum `∑ f p * g p` equals ⟪A,Pproj⟫ (first CS sub-step).
lemma cauchy_schwarz_mixed_sum
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let inner : n → n → ℝ :=
      fun i j => ∑ s,
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
    let f : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * inner p.1 p.2 / Real.sqrt (r p.1 * r p.2)
    let g : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)
    ∑ p : n × n, f p * g p =
      frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) := by
  classical
  intro r inner f g
  -- If a row norm vanishes, the corresponding inner product vanishes.
  have hinner_zero_left : ∀ {i j}, r i = 0 → inner i j = 0 := by
    intro i j hr
    have hP :=
      negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hr (j := j)
    have hinner :=
      Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
    simpa only [hinner] using hP
  have hinner_zero_right : ∀ {i j}, r j = 0 → inner i j = 0 := by
    intro i j hr
    have hP :=
      negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom hr (j := i)
    have hsymm := Pproj_symm (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
    have hP' : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
      simpa only [hsymm] using hP
    have hinner :=
      Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
    simpa only [hinner] using hP'

  have hA_nonneg : ∀ i j, 0 ≤ A i j := hNonneg

  -- Pointwise identity f*g = A_ij * inner_ij.
  have hpoint :
      ∀ p : n × n, f p * g p = A p.1 p.2 * inner p.1 p.2 := by
    intro p
    rcases p with ⟨i,j⟩
    by_cases hzero : r i = 0 ∨ r j = 0
    · have hinner_zero : inner i j = 0 := by
        cases hzero with
        | inl hri => exact hinner_zero_left (i := i) (j := j) hri
        | inr hrj => exact hinner_zero_right (i := i) (j := j) hrj
      simp only [dite_eq_ite, hzero, ↓reduceIte, mul_zero, hinner_zero, f, g]
    · have hpos_i : 0 ≤ r i := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
      have hpos_j : 0 ≤ r j := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
      have hpos_prod_nonneg : 0 ≤ r i * r j := mul_nonneg hpos_i hpos_j
      have hne_i : r i ≠ 0 := by intro h; exact hzero (Or.inl h)
      have hne_j : r j ≠ 0 := by intro h; exact hzero (Or.inr h)
      have hpos_i' : 0 < r i := lt_of_le_of_ne hpos_i (by intro h; exact hne_i h.symm)
      have hpos_j' : 0 < r j := lt_of_le_of_ne hpos_j (by intro h; exact hne_j h.symm)
      have hpos_prod : 0 < r i * r j := mul_pos hpos_i' hpos_j'
      have hroot_ne : Real.sqrt (r i * r j) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos_prod)
      have hcancel :
          (Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j)) *
              (Real.sqrt (A i j) * Real.sqrt (r i * r j)) =
            Real.sqrt (A i j) * Real.sqrt (A i j) * inner i j := by
        field_simp [hroot_ne, mul_comm, mul_left_comm, mul_assoc]
      calc
        f (i,j) * g (i,j)
            = (Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j)) *
                (Real.sqrt (A i j) * Real.sqrt (r i * r j)) := by
                  simp only [div_eq_mul_inv, mul_comm, mul_left_comm, dite_eq_ite, hzero,
                    ↓reduceIte, mul_assoc, f, g]
        _ = (Real.sqrt (A i j))^2 * inner i j := by
              calc
                (Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j)) *
                    (Real.sqrt (A i j) * Real.sqrt (r i * r j))
                    = Real.sqrt (A i j) * Real.sqrt (A i j) * inner i j := hcancel
                _ = (Real.sqrt (A i j))^2 * inner i j := by ring
        _ = A i j * inner i j := by
              have hsq := Real.sq_sqrt (hA_nonneg i j)
              simp only [hsq]

  -- Sum over pairs to relate to `frobeniusInner`.
  have hsum :
      ∑ p : n × n, A p.1 p.2 * inner p.1 p.2 =
        ∑ i, ∑ j, A i j * inner i j := by
    classical
    simpa only [Finset.univ_product_univ] using
      (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f := fun p : n × n =>
        A p.1 p.2 * inner p.1 p.2))

  have hinnerP :
      ∀ i j, inner i j = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j := by
    intro i j
    symm
    exact Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j

  calc
    ∑ p, f p * g p = ∑ p : n × n, A p.1 p.2 * inner p.1 p.2 := by
      refine Finset.sum_congr rfl ?_
      intro p hp; exact hpoint p
    _ = ∑ i, ∑ j, A i j * inner i j := hsum
    _ = frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) := by
          simp only [hinnerP, frobeniusInner, inner]

-- Cauchy–Schwarz bound on the mixed sum, expressed with the same shorthands as above.
lemma cauchy_schwarz_mixed_bound
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let inner : n → n → ℝ :=
      fun i j => ∑ s,
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
    let f : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * inner p.1 p.2 / Real.sqrt (r p.1 * r p.2)
    let g : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)
    (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom))^2 ≤
      (∑ p : n × n, (f p)^2) * (∑ p : n × n, (g p)^2) := by
  classical
  intro r inner f g
  have hfg :
      ∑ p : n × n, f p * g p =
        frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) := by
    simpa only [r, f, g, dite_eq_ite, mul_ite, mul_zero, ite_mul, zero_mul] using
      (cauchy_schwarz_mixed_sum (A := A) (n := n) (μ := μ) hHerm hNonneg ht hBottom)
  have hcs := cauchy_schwarz_sum_square (f := f) (g := g)
  calc
    (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom))^2
        = (∑ p : n × n, f p * g p)^2 := by simp only [hfg]
    _ ≤ (∑ p : n × n, (f p)^2) * (∑ p : n × n, (g p)^2) := hcs


-- Bound the g-part: ∑ (g p)^2 collapses to a weighted sum over A and row norms.
lemma sum_g_sq_expand
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let g : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)
    ∑ p : n × n, (g p)^2 = ∑ i, ∑ j, A i j * (r i) * (r j) := by
  classical
  intro r g
  have hA_nonneg : ∀ i j, 0 ≤ A i j := hNonneg
  -- Pointwise simplification.
  have hpoint :
      ∀ p : n × n, (g p)^2 =
        A p.1 p.2 * r p.1 * r p.2 := by
    intro p
    rcases p with ⟨i,j⟩
    by_cases hzero : r i = 0 ∨ r j = 0
    · have hr_prod : r i * r j = 0 := by
        cases hzero with
        | inl hri => simp only [hri, zero_mul]
        | inr hrj => simp only [hrj, mul_comm, zero_mul]
      have hRHS : A i j * r i * r j = 0 := by
        calc
          A i j * r i * r j = A i j * (r i * r j) := by ring
          _ = A i j * 0 := by simp only [hr_prod, mul_zero]
          _ = 0 := by ring
      simp only [dite_eq_ite, hzero, ↓reduceIte, pow_two, mul_zero, hRHS, g]
    · have hpos_i : 0 ≤ r i := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
      have hpos_j : 0 ≤ r j := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
      have hpos_prod : 0 ≤ r i * r j := mul_nonneg hpos_i hpos_j
      have hsqrtA_sq : (Real.sqrt (A i j))^2 = A i j := Real.sq_sqrt (hA_nonneg i j)
      have hsqrtR_sq : (Real.sqrt (r i * r j))^2 = r i * r j := Real.sq_sqrt hpos_prod
      have hsq : (Real.sqrt (A i j) * Real.sqrt (r i * r j))^2 =
          A i j * (r i * r j) := by
        ring_nf
        simp only [hsqrtA_sq, hsqrtR_sq, mul_comm]
      simp only [dite_eq_ite, hzero, ↓reduceIte, hsq, mul_assoc, g]

  -- Rewrite the double sum using the pointwise identity.
  have hsum :
      ∑ p : n × n, A p.1 p.2 * r p.1 * r p.2 =
        ∑ i, ∑ j, A i j * r i * r j := by
    classical
    simpa only [Finset.univ_product_univ] using
      (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f := fun p : n × n =>
        A p.1 p.2 * r p.1 * r p.2))

  calc
    ∑ p : n × n, (g p)^2 = ∑ p : n × n, A p.1 p.2 * r p.1 * r p.2 := by
      refine Finset.sum_congr rfl ?_
      intro p hp; simp only [hpoint p]
    _ = ∑ i, ∑ j, A i j * r i * r j := hsum

-- Bound the f-part by the g-part pointwise, hence on the sum of squares.
lemma sum_f_sq_le_sum_g_sq
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let inner : n → n → ℝ :=
      fun i j => ∑ s,
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
    let f : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * inner p.1 p.2 / Real.sqrt (r p.1 * r p.2)
    let g : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)
    ∑ p : n × n, (f p)^2 ≤ ∑ p : n × n, (g p)^2 := by
  classical
  intro r inner f g
  have hpoint : ∀ p : n × n, (f p)^2 ≤ (g p)^2 := by
    intro p; rcases p with ⟨i,j⟩
    by_cases hzero : r i = 0 ∨ r j = 0
    · simp only [dite_eq_ite, hzero, ↓reduceIte, pow_two, mul_zero, le_refl, f, g]
    · have hpos_i : 0 ≤ r i := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
      have hpos_j : 0 ≤ r j := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
      have hpos_prod : 0 ≤ r i * r j := mul_nonneg hpos_i hpos_j
      have hpos_prod' : 0 < r i * r j := by
        have hne_i : r i ≠ 0 := by intro h; exact hzero (Or.inl h)
        have hne_j : r j ≠ 0 := by intro h; exact hzero (Or.inr h)
        have hpos_i' : 0 < r i := lt_of_le_of_ne hpos_i (by intro h; exact hne_i h.symm)
        have hpos_j' : 0 < r j := lt_of_le_of_ne hpos_j (by intro h; exact hne_j h.symm)
        exact mul_pos hpos_i' hpos_j'
      have hPij : inner i j = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j := by
        symm; exact Pproj_entry_as_row_inner
          (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
      have hri_sq : (r i)^2 = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
        have hsq := negRowNorm_sq_eq_Pdiag
          (A := A) (n := n) (μ := μ) hHerm ht hBottom i
        simpa only [pow_two] using hsq
      have hrj_sq : (r j)^2 = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j := by
        have hsq := negRowNorm_sq_eq_Pdiag
          (A := A) (n := n) (μ := μ) hHerm ht hBottom j
        simpa only [pow_two] using hsq
      have hdiag : (inner i j)^2 ≤ (r i)^2 * (r j)^2 := by
        have hineq := Pproj_entry_sq_le_diag
          (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
        simpa only [hPij, pow_two, hri_sq, hrj_sq, ge_iff_le] using hineq
      have hdiag' : (inner i j)^2 ≤ (r i * r j)^2 := by
        have hmul_sq : (r i)^2 * (r j)^2 = (r i * r j)^2 := by ring
        simpa only [ge_iff_le, hmul_sq] using hdiag
      have hfrac : (inner i j)^2 / (r i * r j) ≤ r i * r j := by
        have hpos_den : 0 < r i * r j := hpos_prod'
        have hdiv : (inner i j)^2 / (r i * r j) ≤ (r i * r j)^2 / (r i * r j) := by
          have htarget : (inner i j)^2 ≤ (r i * r j)^2 := hdiag'
          have hnonneg_den : 0 ≤ r i * r j := hpos_prod
          exact div_le_div_of_nonneg_right htarget hnonneg_den
        have hcancel : (r i * r j)^2 / (r i * r j) = r i * r j := by
          have hne : r i * r j ≠ 0 := ne_of_gt hpos_den
          field_simp [pow_two, hne, mul_comm, mul_left_comm, mul_assoc]
        linarith
      have hA_nonneg : 0 ≤ A i j := hNonneg i j
      have hf_sq : (f (i,j))^2 = A i j * (inner i j)^2 / (r i * r j) := by
        have hsqrtA_sq : (Real.sqrt (A i j))^2 = A i j := Real.sq_sqrt hA_nonneg
        have hsqrtR_sq : (Real.sqrt (r i * r j))^2 = r i * r j := Real.sq_sqrt hpos_prod
        have hdef : f (i,j) = Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j) := by
          simp only [dite_eq_ite, hzero, ↓reduceIte, f]
        calc
          (f (i,j))^2 = (Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j))^2
             := by simp only [hdef]
          _ = (Real.sqrt (A i j))^2 * (inner i j)^2 / (Real.sqrt (r i * r j))^2 := by ring
          _ = A i j * (inner i j)^2 / (r i * r j) := by simp only [hsqrtA_sq, pow_two, hsqrtR_sq]
      have hmul_le : (f (i,j))^2 ≤ A i j * (r i * r j) := by
        have hmul : A i j * (inner i j)^2 / (r i * r j) ≤ A i j * (r i * r j) := by
          have hmul' := mul_le_mul_of_nonneg_left hfrac hA_nonneg
          have hrew :
              A i j * (inner i j)^2 / (r i * r j) =
                A i j * ((inner i j)^2 / (r i * r j)) := by
            ring_nf
          linarith [hrew]
        linarith [hf_sq, hmul]
      have hdef_g : g (i,j) = Real.sqrt (A i j) * Real.sqrt (r i * r j) := by
        simp only [dite_eq_ite, hzero, ↓reduceIte, g]
      have hg_sq : (g (i,j))^2 = A i j * (r i * r j) := by
        calc
          (g (i,j))^2 = (Real.sqrt (A i j) * Real.sqrt (r i * r j))^2 := by simp only [hdef_g]
          _ = (Real.sqrt (A i j))^2 * (Real.sqrt (r i * r j))^2 := by ring
          _ = A i j * (r i * r j) := by
                have hsqrtA_sq : (Real.sqrt (A i j))^2 = A i j := Real.sq_sqrt (hNonneg i j)
                have hsqrtR_sq : (Real.sqrt (r i * r j))^2 = r i * r j := Real.sq_sqrt hpos_prod
                simp only [hsqrtA_sq, hsqrtR_sq]
      calc
        (f (i,j))^2 ≤ A i j * (r i * r j) := hmul_le
        _ = (g (i,j))^2 := hg_sq.symm
  refine Finset.sum_le_sum (fun p hp => hpoint p)

-- Bound the `g`-sum using ‖A‖ ≤ 1 and `∑ r_i^2 = 1`.
lemma sum_g_sq_le_one
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) (hOp : ‖A‖ ≤ (1 : ℝ))
    {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let g : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)
    ∑ p : n × n, (g p)^2 ≤ 1 := by
  classical
  intro r g
  -- Expand the sum using the previous lemma.
  have hsum := sum_g_sq_expand (A := A) (n := n) (μ := μ) hHerm hNonneg ht hBottom
  have hsum_eq : ∑ p : n × n, (g p)^2 =
      ∑ i, ∑ j, A i j * r i * r j := by
    simpa only [r, g, dite_eq_ite, ite_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      hsum
  -- Identify ∑ r_i^2 via the diagonal of `Pproj`.
  have hdiag : ∀ i, (r i)^2 = Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
    intro i
    have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
    simpa only [pow_two] using hsq
  have htrace :
      Matrix.trace (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) = 1 := by
    simpa only [Pproj, UsMatrix] using
      (negUsub_trace_one (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
  have hsum_rsq : ∑ i, (r i)^2 = 1 := by
    calc
      ∑ i, (r i)^2 = ∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
        classical
        simp only [hdiag]
      _ = 1 := by simpa only [trace, diag_apply] using htrace
  -- View `r` as a Euclidean vector.
  let rvec : EuclideanSpace ℝ n := (EuclideanSpace.equiv n ℝ).symm r
  let mulVecE : EuclideanSpace ℝ n :=
    (EuclideanSpace.equiv n ℝ).symm (Matrix.mulVec A r)
  -- Coordinate evaluations.
  have rvec_apply : ∀ i, rvec i = r i := by
    intro i
    simp only [PiLp.continuousLinearEquiv_symm_apply, rvec]
  have hdot_sum : dotProduct rvec mulVecE = ∑ x, rvec.ofLp x * mulVecE.ofLp x := by
    classical
    simp only [dotProduct]
  have hinner_sum : inner ℝ rvec mulVecE = ∑ x, rvec.ofLp x * mulVecE.ofLp x := by
    classical
    -- `inner` on `EuclideanSpace` is given by the dot product with reversed arguments.
    calc
      inner ℝ rvec mulVecE =
          dotProduct (mulVecE.ofLp) (rvec.ofLp) := by
        simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
      _ = ∑ x, mulVecE.ofLp x * rvec.ofLp x := by
        simp only [dotProduct]
      _ = ∑ x, rvec.ofLp x * mulVecE.ofLp x := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        ring
  have hdot :
      ∑ i, ∑ j, A i j * r i * r j =
        inner ℝ rvec mulVecE := by
    classical
    have hrewrite :
        ∑ i, ∑ j, A i j * r i * r j =
          ∑ i, r i * (∑ j, A i j * r j) := by
      simp only [mul_assoc, Finset.mul_sum, mul_left_comm]
    have hdot' :
        ∑ i, ∑ j, A i j * r i * r j = dotProduct rvec mulVecE := by
      calc
        ∑ i, ∑ j, A i j * r i * r j = ∑ i, r i * (∑ j, A i j * r j) := hrewrite
        _ = dotProduct rvec mulVecE := by
          simp only [dotProduct, PiLp.continuousLinearEquiv_symm_apply, mulVec, rvec, mulVecE]
    calc
      ∑ i, ∑ j, A i j * r i * r j = dotProduct rvec mulVecE := hdot'
      _ = ∑ x, rvec.ofLp x * mulVecE.ofLp x := hdot_sum
      _ = inner ℝ rvec mulVecE := hinner_sum.symm
  have hr_nonneg : ∀ i, 0 ≤ rvec i := by
    intro i; simpa only [PiLp.continuousLinearEquiv_symm_apply] using
      negRowNorm_nonneg (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
  have hr_nonneg_r : ∀ i, 0 ≤ r i := by
    intro i
    have := hr_nonneg i
    simpa only [ge_iff_le, PiLp.continuousLinearEquiv_symm_apply] using this
  have hmulVec_nonneg : ∀ i, 0 ≤ mulVecE i := by
    intro i
    have :
        0 ≤ ∑ j, A i j * r j := by
      refine Finset.sum_nonneg (fun j _ => ?_)
      nlinarith [hNonneg i j, hr_nonneg_r j]
    simpa only [PiLp.continuousLinearEquiv_symm_apply, mulVec, dotProduct, ge_iff_le] using this
  -- Nonnegativity of the inner product (coordinatewise nonnegativity).
  have hdot_nonneg : 0 ≤ dotProduct rvec mulVecE := by
    classical
    have hsum :
        0 ≤ ∑ i : n, rvec i * mulVecE i := by
      refine Finset.sum_nonneg ?_
      intro i hi
      exact mul_nonneg (hr_nonneg i) (hmulVec_nonneg i)
    simpa only [dotProduct, ge_iff_le] using hsum
  have hinner_nonneg : 0 ≤ inner ℝ rvec mulVecE := by
    have hsum_nonneg : 0 ≤ ∑ x, rvec.ofLp x * mulVecE.ofLp x := by
      simpa only [hdot_sum] using hdot_nonneg
    -- Rewrite the inner product as the same coordinatewise sum.
    nlinarith [hinner_sum, hsum_nonneg]
  -- Cauchy–Schwarz on the inner product.
  have hcs :
      inner ℝ rvec mulVecE ≤
        ‖rvec‖ * ‖mulVecE‖ := by
    have habs : |inner ℝ rvec mulVecE| ≤ ‖rvec‖ * ‖mulVecE‖ :=
      abs_real_inner_le_norm (x := rvec) (y := mulVecE)
    have habs_eq : |inner ℝ rvec mulVecE| = inner ℝ rvec mulVecE :=
      abs_of_nonneg hinner_nonneg
    linarith
  have hmulvec_norm :
      ‖mulVecE‖ ≤ ‖A‖ * ‖rvec‖ :=
    by
      -- the Euclidean equivalence is the identity on norms
      simpa only [PiLp.continuousLinearEquiv_symm_apply] using
        (Matrix.l2_opNorm_mulVec (A := A) (x := rvec))
  have hr_norm_sq : ‖rvec‖^2 = (1 : ℝ) := by
    classical
    -- Expand the norm square as the sum of coordinate squares.
    have hnorm_sq : ‖rvec‖^2 = ∑ i, ‖rvec i‖^2 := by
      -- `EuclideanSpace.norm_sq_eq` specializes the general PiLp formula.
      simpa only [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_sq_eq (x := rvec))
    have hr_abs : ∀ i, ‖rvec i‖ = r i := by
      intro i
      have hnonneg := hr_nonneg i
      have hval : rvec i = r i := rvec_apply i
      -- `rvec i` is nonnegative, so its absolute value is itself.
      have habs : |rvec i| = rvec i := abs_of_nonneg hnonneg
      simpa only [hval, Real.norm_eq_abs, abs_eq_self, ge_iff_le]
    calc
      ‖rvec‖^2 = ∑ i, ‖rvec i‖^2 := hnorm_sq
      _ = ∑ i, (r i)^2 := by
        simp only [hr_abs, pow_two]
      _ = 1 := hsum_rsq
  have hr_norm : ‖rvec‖ = (1 : ℝ) := by
    have hnonneg : 0 ≤ ‖rvec‖ := norm_nonneg _
    nlinarith
  have hdot_le_norm :
      inner ℝ rvec mulVecE ≤ ‖A‖ := by
    have hstep : ‖rvec‖ * ‖mulVecE‖ ≤ ‖rvec‖ * (‖A‖ * ‖rvec‖) := by
      have hnonneg : 0 ≤ ‖rvec‖ := norm_nonneg _
      have hmul := mul_le_mul_of_nonneg_left hmulvec_norm hnonneg
      simpa only [mul_left_comm, ge_iff_le] using hmul
    have hbound := le_trans hcs hstep
    nlinarith
  have hquad_le_one :
      ∑ i, ∑ j, A i j * r i * r j ≤ (1 : ℝ) := by
    have := hdot_le_norm
    have hA_le : ‖A‖ ≤ (1 : ℝ) := hOp
    have h := le_trans this hA_le
    simpa only [hdot, ge_iff_le] using h
  have hsum_le_one : ∑ p : n × n, (g p)^2 ≤ (1 : ℝ) := by
    linarith [hsum_eq, hquad_le_one]
  exact hsum_le_one
-- Write ⟪A,Pproj⟫ as a triple sum over i,j,s using the row vectors.
lemma frobeniusInner_A_Pproj_triple_sum
    (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) =
      ∑ i, ∑ j, ∑ s,
        A i j *
          (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s) *
          (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s) := by
  classical
  -- Start from the double-sum expression and substitute the row inner product.
  have hdouble := frobeniusInner_A_Pproj_explicit (A := A) (n := n) (μ := μ) hHerm ht hBottom
  calc
    frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom)
        = ∑ i, ∑ j, A i j * Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j := hdouble
    _ = ∑ i, ∑ j, A i j * ∑ s,
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
            negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp only [Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
                j]
    _ = ∑ i, ∑ j, ∑ s,
          A i j *
            (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s) *
            (negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s) := by
          -- pull `A i j` inside the innermost sum
          refine Finset.sum_congr rfl ?_
          intro i hi
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp only [Finset.mul_sum, mul_assoc]

-- Pointwise expression for a `negWitnessM` entry in terms of the row correlation and norms.
lemma negWitnessM_entry_inner_norms
    (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (i j : n) :
    negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j =
      if _ : negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i = 0 ∨
          negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j = 0 then
        0
      else
        (∑ s,
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s) ^ 2 /
          (negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i *
            negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j) := by
  classical
  -- Shorthands.
  let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  let inner : n → n → ℝ :=
    fun i j => ∑ s,
      negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
  by_cases hzero : r i = 0 ∨ r j = 0
  · -- If either norm is zero, both sides vanish.
    rcases hzero with hri | hrj
    · have hri' :
        negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i = 0 := by
        simpa only using hri
      have hdiag :
          Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0 := by
        have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
        nlinarith
      have hentry_zero :
          negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j = 0 :=
        negWitnessM_entry_zero_left (A := A) (n := n) (μ := μ) (t := t)
          hHerm ht hBottom hdiag (i := i) (j := j)
      have hinner_zero :
          inner i j = 0 := by
        have hrow :=
          negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom hri' (j := j)
        have hP :=
          Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom i j
        simpa only [hP] using hrow
      simp only [hentry_zero, hri, true_or, ↓reduceDIte, r]
    · have hrj' :
        negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j = 0 := by
        simpa only using hrj
      have hdiag :
          Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0 := by
        have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom j
        nlinarith
      have hentry_zero :
          negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j = 0 :=
        negWitnessM_entry_zero_right (A := A) (n := n) (μ := μ) (t := t)
          hHerm ht hBottom hdiag (i := i) (j := j)
      have hinner_zero :
          inner i j = 0 := by
        have hrow :=
          negRowNorm_zero_row_zero (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom hrj' (j := i)
        have hP :=
          Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t)
            hHerm ht hBottom i j
        have hsymm := Pproj_symm (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
        have hzero' : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = 0 := by
          simpa only [hsymm] using hrow
        simpa only [hP] using hzero'
      simp only [hentry_zero, hrj, or_true, ↓reduceDIte, r]
  · -- Both norms are nonzero: use the positive-diagonal formula.
    have hri_pos : 0 < r i := by
      have hnonneg := negRowNorm_nonneg (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
      have hne : 0 ≠ r i := by
        intro h; exact hzero (Or.inl h.symm)
      exact lt_of_le_of_ne hnonneg hne
    have hrj_pos : 0 < r j := by
      have hnonneg := negRowNorm_nonneg (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
      have hne : 0 ≠ r j := by
        intro h; exact hzero (Or.inr h.symm)
      exact lt_of_le_of_ne hnonneg hne
    -- Convert the positive norms into positive diagonals.
    have hPii_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i := by
      have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom i
      nlinarith
    have hPjj_pos : 0 < Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j := by
      have hsq := negRowNorm_sq_eq_Pdiag (A := A) (n := n) (μ := μ) hHerm ht hBottom j
      nlinarith
    have hentry :=
      negWitnessM_entry_pos_diag (A := A) (n := n) (μ := μ) (t := t)
        hHerm ht hBottom i j hPii_pos hPjj_pos
    have hPij :
        Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j = inner i j := by
      symm
      exact Pproj_entry_as_row_inner (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
    simp only [hentry, hPij, hzero, ↓reduceDIte, inner, r]

-- Identify the `f`-sum with ⟪A, negWitnessM⟫.
lemma sum_f_sq_eq_frobeniusInner_negWitnessM
    (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
    let inner : n → n → ℝ :=
      fun i j => ∑ s,
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
          negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
    let f : n × n → ℝ := fun p =>
      if _ : r p.1 = 0 ∨ r p.2 = 0 then 0
      else Real.sqrt (A p.1 p.2) * inner p.1 p.2 / Real.sqrt (r p.1 * r p.2)
    ∑ p : n × n, (f p)^2 =
      frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) := by
  classical
  intro r inner f
  have hA_nonneg : ∀ i j, 0 ≤ A i j := hNonneg
  have hpoint :
      ∀ p : n × n, (f p)^2 =
        A p.1 p.2 * (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) p.1 p.2 := by
    intro p; rcases p with ⟨i,j⟩
    by_cases hzero : r i = 0 ∨ r j = 0
    · -- Both sides vanish.
      have hentry :=
        negWitnessM_entry_inner_norms (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
      simp only [dite_eq_ite, hzero, ↓reduceIte, pow_two, mul_zero, hentry, ↓reduceDIte, f, r,
        inner]
    · -- Nonzero norms: expand both sides.
      have hpos_i : 0 ≤ r i := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i
      have hpos_j : 0 ≤ r j := negRowNorm_nonneg
        (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j
      have hpos_prod : 0 ≤ r i * r j := mul_nonneg hpos_i hpos_j
      have hsqrtA_sq : (Real.sqrt (A i j))^2 = A i j := Real.sq_sqrt (hA_nonneg i j)
      have hsqrtR_sq : (Real.sqrt (r i * r j))^2 = r i * r j := Real.sq_sqrt hpos_prod
      have hdef : f (i,j) = Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j) := by
        simp only [dite_eq_ite, hzero, ↓reduceIte, f]
      have hentry :=
        negWitnessM_entry_inner_norms (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j
      have hentry' :
          negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j =
            (inner i j)^2 / (r i * r j) := by
        have h := hentry
        simp only [hzero, ↓reduceDIte, r] at h
        exact h
      have hf_sq :
          (f (i,j))^2 = A i j * (inner i j)^2 / (r i * r j) := by
        calc
          (f (i,j))^2 = (Real.sqrt (A i j) * inner i j / Real.sqrt (r i * r j))^2 := by
            simp only [hdef]
          _ = (Real.sqrt (A i j))^2 * (inner i j)^2 / (Real.sqrt (r i * r j))^2 := by ring
          _ = A i j * (inner i j)^2 / (r i * r j) := by simp only [hsqrtA_sq, pow_two, hsqrtR_sq]
      calc
        (f (i,j))^2 = A i j * (inner i j)^2 / (r i * r j) := hf_sq
        _ = A i j * ((inner i j)^2 / (r i * r j)) := by ring
        _ = A i j * (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i j) := by
              simp only [hentry']
  have hsum :
      ∑ p : n × n, (f p)^2 =
        ∑ i, ∑ j,
          A i j *
            (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j := by
    classical
    calc
      ∑ p : n × n, (f p)^2
          = ∑ p : n × n,
              A p.1 p.2 *
                (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) p.1 p.2 := by
                refine Finset.sum_congr rfl ?_
                intro p hp; simpa only using hpoint p
      _ = ∑ i, ∑ j,
          A i j *
            (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j := by
                simpa only [Finset.univ_product_univ] using
                  (Finset.sum_product (s := Finset.univ) (t := Finset.univ) (f := fun p : n × n =>
                    A p.1 p.2 *
                      (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) p.1 p.2))
  -- Translate the double sum as the Frobenius inner product.
  simpa only [frobeniusInner] using hsum

-- Rewrite `frobeniusInner A (negWitnessM …)` as the explicit double sum using the entry formula.
lemma frobeniusInner_negWitnessM_explicit
    (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
      ∑ i, ∑ j,
        A i j *
          (if _ : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0 then 0
           else if _ : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0 then 0
           else
             (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
               (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
                Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j))) := by
  classical
  -- Entrywise explicit formula.
  have hentry :=
    negWitnessM_entry_formula (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  calc
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
        = ∑ i, ∑ j, A i j *
            (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j := rfl
    _ = ∑ i, ∑ j, A i j *
        (if hPi : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 0 then 0
         else if hPj : Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j = 0 then 0
         else
           (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j) ^ 2 /
             (Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
              Real.sqrt (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j))) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      refine Finset.sum_congr rfl ?_
      intro j hj
      -- Substitute the entry formula at `(i,j)`.
      have h := hentry i j
      simp only [h, dite_eq_ite, mul_ite, mul_zero]

-- If one diagonal of `Pproj` vanishes, the corresponding entry of `negWitnessM` is zero.
-- Frobenius bound for `negWitnessM` using the projection inequalities.
lemma Pproj_frobeniusSq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) = 1 / (t : ℝ) := by
  classical
  simpa only [Pproj, UsMatrix, one_div] using
    (negUsub_frobeniusSq (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)

lemma negWitnessM_frobeniusSq_le_Pproj
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) ≤
      frobeniusSq (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) := by
  classical
  have hsum :
      ∑ i, ∑ j,
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 ≤
        ∑ i, ∑ j,
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j)^2 := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    simpa only using
      negWitnessM_entry_sq_le_Pproj_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom i j
  have hfrobM :
      frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
        ∑ i, ∑ j,
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 := by
    simp only [frobeniusSq]
  have hfrobP :
      frobeniusSq (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) =
        ∑ i, ∑ j,
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i j)^2 := by
    simp only [frobeniusSq]
  linarith

lemma negWitnessM_frobeniusSq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t)
      hHerm ht hBottom) ≤ 1 / (t : ℝ) := by
  classical
  have hP := Pproj_frobeniusSq (A := A) (n := n) (μ := μ) hHerm ht hBottom
  have hbound := negWitnessM_frobeniusSq_le_Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom
  linarith

lemma negWitnessM_inner_lower
    {μ : ℝ} (hHerm : A.IsHermitian) (hNonneg : ∀ i j, 0 ≤ A i j) (hOp : ‖A‖ ≤ (1 : ℝ))
    {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) (hμ : 0 ≤ μ) :
    frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) ≥ μ^2 := by
  classical
  -- Shorthands.
  let r : n → ℝ := negRowNorm (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  let inner : n → n → ℝ :=
    fun i j => ∑ s,
      negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom i s *
        negRow (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom j s
  let f : n × n → ℝ := fun p =>
    if h : r p.1 = 0 ∨ r p.2 = 0 then 0
    else Real.sqrt (A p.1 p.2) * inner p.1 p.2 / Real.sqrt (r p.1 * r p.2)
  let g : n × n → ℝ := fun p =>
    if h : r p.1 = 0 ∨ r p.2 = 0 then 0
    else Real.sqrt (A p.1 p.2) * Real.sqrt (r p.1 * r p.2)

  -- Cauchy–Schwarz on the mixed sum.
  have hcs :=
    cauchy_schwarz_mixed_bound (A := A) (n := n) (μ := μ) hHerm hNonneg ht hBottom
  have hcs' :
      (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom))^2 ≤
        (∑ p : n × n, (f p)^2) * (∑ p : n × n, (g p)^2) := by
    simpa only [r, inner, f, g, dite_eq_ite, ite_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      hcs
  -- Identify the `f`-sum with ⟪A, negWitnessM⟫.
  have hsum_f :=
    sum_f_sq_eq_frobeniusInner_negWitnessM (A := A) (n := n) (μ := μ) hHerm hNonneg ht hBottom
  have hsum_f' :
      ∑ p : n × n, (f p)^2 =
        frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) := by
    simpa only [r, inner, f, dite_eq_ite, ite_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      hsum_f
  -- Bound the `g`-sum using ‖A‖ ≤ 1.
  have hsum_g :=
    sum_g_sq_le_one (A := A) (n := n) (μ := μ) hHerm hNonneg hOp ht hBottom
  have hsum_g' : ∑ p : n × n, (g p)^2 ≤ 1 := by
    simpa only [r, g, dite_eq_ite, ite_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using
      hsum_g
  have hnonneg_f : 0 ≤ ∑ p : n × n, (f p)^2 := by positivity
  -- From CS, isolate the `f`-sum.
  have hbound :
      (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom))^2 ≤
        ∑ p : n × n, (f p)^2 := by
    have hmul_le :
        (∑ p : n × n, (f p)^2) * (∑ p : n × n, (g p)^2) ≤
          (∑ p : n × n, (f p)^2) * 1 := by
      have := hsum_g'
      have hmul := mul_le_mul_of_nonneg_left this hnonneg_f
      nlinarith
    have hcs'' := hcs'
    linarith
  -- Lower bound from `Pproj`.
  have hP_sq_ge :=
    frobeniusInner_A_Pproj_sq_ge (A := A) (n := n) (μ := μ) hHerm ht hBottom hμ
  -- Combine.
  have hfinal :
      μ^2 ≤ frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t)
        hHerm ht hBottom) := by
    have hbound' : (frobeniusInner A (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom))^2 ≤
        frobeniusInner A (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) := by
      simpa only [hsum_f'] using hbound
    linarith
  simpa only [ge_iff_le] using hfinal

end FrobeniusBound

-- Frobenius bound helpers outside the section.
lemma Pproj_trace_one
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    Matrix.trace (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom) = 1 := by
  classical
  simpa only [Pproj, UsMatrix] using
    (negUsub_trace_one (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)

lemma negWitnessM_frobeniusSq_le_trace_sq
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) ≤
      (∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) ^ 2 := by
  classical
  -- Entrywise bound summed over all entries.
  have hsum :
      ∑ i, ∑ j,
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 ≤
        ∑ i, ∑ j,
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine Finset.sum_le_sum (fun j _ => ?_)
    simpa only using (negWitnessM_entry_sq_le (A := A) (n := n) (μ := μ) hHerm ht hBottom i j)
  have hRHS :
      ∑ i, ∑ j,
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
          (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j)
        = (∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
          (∑ j, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := by
    simp only [Finset.mul_sum, mul_comm]
  -- Frobenius norm is the sum of squares of all entries.
  have hfrob :
      frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) =
        ∑ i, ∑ j,
          ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 := by
    simp only [frobeniusSq]
  calc
    frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
        = ∑ i, ∑ j,
            ((negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) i j)^2 := hfrob
    _ ≤ ∑ i, ∑ j,
            (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
            (Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := hsum
    _ = (∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) *
            (∑ j, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom j j) := hRHS
    _ = (∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i) ^ 2 := by ring

lemma negWitnessM_frobeniusSq_le_one
    {μ : ℝ} (hHerm : A.IsHermitian) {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    frobeniusSq (negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom) ≤ 1 := by
  classical
  have htrace := Pproj_trace_one (A := A) (n := n) (μ := μ) hHerm ht hBottom
  have hsum_diag : ∑ i, Pproj (A := A) (n := n) (μ := μ) hHerm ht hBottom i i = 1 := by
    simpa only [trace, diag_apply] using htrace
  have hbound := negWitnessM_frobeniusSq_le_trace_sq (A := A) (n := n) (μ := μ) hHerm ht hBottom
  simpa only [ge_iff_le, hsum_diag, one_pow] using hbound

theorem lemma4_4
    (hHerm : A.IsHermitian)
    (hNonneg : ∀ i j, 0 ≤ A i j)
    (hOp : ‖A‖ ≤ (1 : ℝ))
    {μ : ℝ} (hμ : 0 ≤ μ)
    {t : ℕ} (ht : 0 < t)
    (hBottom : bottomThresholdRank A hHerm μ ≥ t) :
    ∃ M : Matrix n n ℝ,
      Matrix.PosSemidef M ∧
      Matrix.trace M = 1 ∧
      frobeniusSq M ≤ 1 / (t : ℝ) ∧
      frobeniusInner A M ≥ μ^2 := by
  classical
  -- Choose the explicit witness `M := negWitnessM`.
  let M := negWitnessM (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom
  refine ⟨M,
    negWitnessM_posSemidef (A := A) (n := n) (μ := μ) hHerm ht hBottom,
    ?trace, ?frob, ?inner⟩
  · -- Trace = 1.
    simpa only using (negWitnessM_trace_one (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
  · -- Frobenius bound.
    simpa only [one_div] using
      (negWitnessM_frobeniusSq (A := A) (n := n) (μ := μ) (t := t) hHerm ht hBottom)
  · -- Inner-product bound (imported from the spectral argument).
    simpa only [ge_iff_le] using
      (negWitnessM_inner_lower (A := A) (n := n) (μ := μ) (t := t) hHerm hNonneg hOp ht hBottom hμ)

end Lemma4_4

end ThresholdRank
