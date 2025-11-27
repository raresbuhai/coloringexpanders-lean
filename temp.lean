import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Data.Real.StarOrdered

open Matrix BigOperators

open scoped Matrix.Norms.L2Operator

namespace ThresholdRank

variable {n : Type*} [Fintype n] [DecidableEq n]

noncomputable def topThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) : ℕ :=
  Fintype.card { i : n // τ ≤ hA.eigenvalues i }

/-- Bottom threshold rank: number of eigenvalues `≤ -μ`.

This is `| { i : n // λᵢ ≤ -μ } |` where `λᵢ = hA.eigenvalues i`. -/
noncomputable def bottomThresholdRank
    (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) : ℕ :=
  Fintype.card { i : n // hA.eigenvalues i ≤ -μ }

@[simp]
lemma topThresholdRank_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian) (τ : ℝ) :
    0 ≤ topThresholdRank A hA τ := Nat.zero_le _

@[simp]
lemma bottomThresholdRank_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian) (μ : ℝ) :
    0 ≤ bottomThresholdRank A hA μ := Nat.zero_le _

lemma topThresholdRank_antitone
    (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    Antitone (fun τ => topThresholdRank A hA τ) := by
  classical
  intro τ₁ τ₂ hτ
  simpa [topThresholdRank] using
    (Fintype.card_subtype_mono
      (p := fun i => τ₂ ≤ hA.eigenvalues i)
      (q := fun i => τ₁ ≤ hA.eigenvalues i)
      (fun _ hi => hτ.trans hi))

end ThresholdRank
