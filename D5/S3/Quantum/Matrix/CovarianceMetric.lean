/- GID: D5/S3/Quantum/Matrix/CovarianceMetric
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/CovarianceMetric
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Rectangular covariance-metric completion and positive-metric Riccati trace minimization. -/

import D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

/-!
Covariance metrics over complex matrices.  The rectangular results retain the
actual column space and allow singular or zero rectangular factors.  The
Riccati results require the displayed metric matrices to be positive definite,
so every inverse and every attained minimizer is an actual matrix inverse.
These lemmas supply the covariance-metric part of the Audenaert route; they do
not assert the unresolved two-by-N sharp norm-compression conjecture.
-/

/-
admission_basis: escape-witness
proof_shape: rectangular_metric_square=content; rectangular_metric_trace_bound=content;
  metric_square=content; covariance_metric_gap=content; covariance_metric_minimum=content
escape_witness: each public endpoint contains the rectangular completion or the
  Riccati remainder/minimization argument on its live proof path
Direct frozen dependencies: D5.S3.Quantum.Matrix.LinGProperty.GeometricMeanBound
Reg audit: unfinished under linked issue #5214; no declared_validated registration is claimed.
-/

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace D5.S3.Quantum.Matrix.CovarianceMetric

section Rectangular
variable {m k : Type*} [Fintype m] [Fintype k]
  [DecidableEq m] [DecidableEq k]

/-- Completion of the square retaining the actual rectangular column space.
In the original application `C = Z * B`; the factors may be singular or zero. -/
theorem rectangular_metric_square (D : Matrix m m ℂ) (hD : D.PosDef)
    (A C : Matrix m k ℂ) :
    Aᴴ * D * A + Cᴴ * D⁻¹ * C - Aᴴ * C - Cᴴ * A =
      (A - D⁻¹ * C)ᴴ * D * (A - D⁻¹ * C) ∧
    (Aᴴ * D * A + Cᴴ * D⁻¹ * C - Aᴴ * C - Cᴴ * A).PosSemidef := by
  letI := hD.isUnit.invertible
  have hi : (D⁻¹)ᴴ = D⁻¹ := hD.inv.isHermitian.eq
  have h₁ : D * (D⁻¹ * C) = C := by
    calc
      D * (D⁻¹ * C) = (D * D⁻¹) * C := by rw [Matrix.mul_assoc]
      _ = C := by rw [Matrix.mul_inv_of_invertible]; simp
  have h₂ : (D⁻¹ * C)ᴴ * D = Cᴴ := by
    calc
      (D⁻¹ * C)ᴴ * D = Cᴴ * (D⁻¹)ᴴ * D := by
        rw [Matrix.conjTranspose_mul]
      _ = Cᴴ * D⁻¹ * D := by rw [hi]
      _ = Cᴴ := by
        rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]
        simp
  have he : (A - D⁻¹ * C)ᴴ * D * (A - D⁻¹ * C) =
      Aᴴ * D * A + Cᴴ * D⁻¹ * C - Aᴴ * C - Cᴴ * A := by
    calc
      _ = (Aᴴ - (D⁻¹ * C)ᴴ) * D * (A - D⁻¹ * C) := by
        rw [Matrix.conjTranspose_sub]
      _ = (Aᴴ * D - (D⁻¹ * C)ᴴ * D) * (A - D⁻¹ * C) := by
        congr 1
        exact Matrix.sub_mul _ _ _
      _ = (Aᴴ * D - Cᴴ) * (A - D⁻¹ * C) := by rw [h₂]
      _ = Aᴴ * D * A - Aᴴ * D * (D⁻¹ * C) - Cᴴ * A + Cᴴ * (D⁻¹ * C) := by
        simp only [Matrix.sub_mul, Matrix.mul_sub]
        noncomm_ring
      _ = _ := by
        rw [Matrix.mul_assoc Aᴴ D (D⁻¹ * C), h₁]
        simp only [Matrix.mul_assoc]
        abel
  refine ⟨he.symm, ?_⟩
  rw [← he]
  exact hD.posSemidef.conjTranspose_mul_mul_same (A - D⁻¹ * C)

/-- The metric bound follows from an actual PSD square. -/
theorem rectangular_metric_trace_bound (D : Matrix m m ℂ) (hD : D.PosDef)
    (A C : Matrix m k ℂ) :
    2 * (Matrix.trace (Aᴴ * C)).re ≤
      (Matrix.trace (Aᴴ * D * A)).re +
        (Matrix.trace (Cᴴ * D⁻¹ * C)).re := by
  have hp := (rectangular_metric_square D hD A C).2
  have hh := (RCLike.nonneg_iff.mp hp.trace_nonneg).1
  have hc : (Matrix.trace (Cᴴ * A)).re = (Matrix.trace (Aᴴ * C)).re := by
    have ht := Matrix.trace_conjTranspose (Aᴴ * C)
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at ht
    simpa using congrArg Complex.re ht
  simp only [Matrix.trace_add, Matrix.trace_sub, Complex.add_re, Complex.sub_re] at hh
  change 0 ≤ (Matrix.trace (Aᴴ * D * A)).re +
    (Matrix.trace (Cᴴ * D⁻¹ * C)).re -
      (Matrix.trace (Aᴴ * C)).re - (Matrix.trace (Cᴴ * A)).re at hh
  linarith

end Rectangular

section RiccatiMinimum
variable {n : ℕ}

/-- Exact matrix remainder for a nonoptimal positive metric. -/
theorem metric_square (D G : Matrix (Fin n) (Fin n) ℂ)
    (hD : D.PosDef) (hG : G.IsHermitian) :
    D + G * D⁻¹ * G - G - G = (D - G) * D⁻¹ * (D - G) ∧
    ((D - G) * D⁻¹ * (D - G)).PosSemidef := by
  letI := hD.isUnit.invertible
  have h₁ : (D - G) * D⁻¹ = 1 - G * D⁻¹ := by
    rw [sub_mul, Matrix.mul_inv_of_invertible]
  have h₂ : G * D⁻¹ * D = G := by
    rw [Matrix.mul_assoc, Matrix.inv_mul_of_invertible, mul_one]
  constructor
  · symm
    calc
      _ = (1 - G * D⁻¹) * (D - G) := by rw [h₁]
      _ = D - G - G * D⁻¹ * D + G * D⁻¹ * G := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]
        noncomm_ring
      _ = _ := by
        rw [h₂]
        noncomm_ring
  · have hh : (D - G).IsHermitian := hD.isHermitian.sub hG
    simpa only [hh.eq] using
      hD.inv.posSemidef.conjTranspose_mul_mul_same (D - G)

private theorem trace_product_nonneg (P K : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosDef) (hK : K.PosSemidef) :
    0 ≤ (Matrix.trace (K * P)).re := by
  let S := CFC.sqrt P
  have hS : S.IsHermitian := hP.isStrictlyPositive.sqrt.posDef.isHermitian
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.posSemidef.nonneg
  have hp := hK.conjTranspose_mul_mul_same S
  have ht : Matrix.trace (Sᴴ * K * S) = Matrix.trace (K * P) := by
    rw [hS.eq]
    calc
      Matrix.trace (S * K * S) = Matrix.trace ((K * S) * S) := by
        rw [Matrix.mul_assoc, Matrix.trace_mul_comm S (K * S)]
      _ = Matrix.trace (K * (S * S)) := by rw [Matrix.mul_assoc]
      _ = Matrix.trace (K * P) := by rw [hSS]
  have hh := (RCLike.nonneg_iff.mp hp.trace_nonneg).1
  rw [ht] at hh
  exact hh

/-- The repository's geometric mean supplies the exact Riccati cost optimizer. -/
theorem covariance_metric_gap
    (P S D : Matrix (Fin n) (Fin n) ℂ)
    (hP : P.PosDef) (hS : S.PosDef) (hD : D.PosDef) :
    let G := D5.S3.Quantum.Matrix.LinGProperty.geometricMean P⁻¹ S
    (Matrix.trace (D * P)).re + (Matrix.trace (D⁻¹ * S)).re -
        2 * (Matrix.trace (G * P)).re =
      (Matrix.trace (((D - G) * D⁻¹ * (D - G)) * P)).re ∧
    0 ≤ (Matrix.trace (((D - G) * D⁻¹ * (D - G)) * P)).re := by
  letI := hP.isUnit.invertible
  let G := D5.S3.Quantum.Matrix.LinGProperty.geometricMean P⁻¹ S
  have hG : G.PosDef :=
    (D5.S3.Quantum.Matrix.LinGProperty.geometricMean_riccati hP.inv hS).1
  have hR : G * P * G = S := by
    simpa only [Matrix.inv_inv_of_invertible] using
      (D5.S3.Quantum.Matrix.LinGProperty.geometricMean_riccati hP.inv hS).2
  obtain ⟨he, hp⟩ := metric_square D G hD hG.isHermitian
  have hc : Matrix.trace ((G * D⁻¹ * G) * P) =
      Matrix.trace (D⁻¹ * (G * P * G)) := by
    calc
      _ = Matrix.trace (G * (D⁻¹ * G * P)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((D⁻¹ * G * P) * G) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]
  have ht : Matrix.trace (D * P) + Matrix.trace (D⁻¹ * S) -
      2 * Matrix.trace (G * P) =
      Matrix.trace (((D - G) * D⁻¹ * (D - G)) * P) := by
    calc
      _ = Matrix.trace ((D + G * D⁻¹ * G - G - G) * P) := by
        simp only [add_mul, sub_mul, Matrix.trace_add, Matrix.trace_sub]
        rw [hc, hR]
        ring
      _ = _ := congrArg (fun K => Matrix.trace (K * P)) he
  constructor
  · simpa [Complex.mul_re] using congrArg Complex.re ht
  · exact trace_product_nonneg P _ hP hp

/-- Global minimality of the actual trace cost, with its attained value. -/
theorem covariance_metric_minimum
    (P S : Matrix (Fin n) (Fin n) ℂ) (hP : P.PosDef) (hS : S.PosDef) :
    let G := D5.S3.Quantum.Matrix.LinGProperty.geometricMean P⁻¹ S
    G.PosDef ∧ G * P * G = S ∧
    (Matrix.trace (G * P)).re + (Matrix.trace (G⁻¹ * S)).re =
      2 * (Matrix.trace (G * P)).re ∧
    ∀ D : Matrix (Fin n) (Fin n) ℂ, D.PosDef →
      2 * (Matrix.trace (G * P)).re ≤
        (Matrix.trace (D * P)).re + (Matrix.trace (D⁻¹ * S)).re := by
  letI := hP.isUnit.invertible
  let G := D5.S3.Quantum.Matrix.LinGProperty.geometricMean P⁻¹ S
  have hG : G.PosDef :=
    (D5.S3.Quantum.Matrix.LinGProperty.geometricMean_riccati hP.inv hS).1
  have hR : G * P * G = S := by
    simpa only [Matrix.inv_inv_of_invertible] using
      (D5.S3.Quantum.Matrix.LinGProperty.geometricMean_riccati hP.inv hS).2
  letI := hG.isUnit.invertible
  have ht : Matrix.trace (G⁻¹ * S) = Matrix.trace (G * P) := by
    rw [← hR]
    calc
      _ = Matrix.trace (P * G) := by
        simp only [← Matrix.mul_assoc, Matrix.inv_mul_of_invertible, one_mul]
      _ = _ := Matrix.trace_mul_comm _ _
  refine ⟨hG, hR, ?_, ?_⟩
  · rw [ht]
    ring
  · intro D hD
    obtain ⟨he, hp⟩ := covariance_metric_gap P S D hP hS hD
    change _ = (Matrix.trace (((D - G) * D⁻¹ * (D - G)) * P)).re at he
    linarith

end RiccatiMinimum
end D5.S3.Quantum.Matrix.CovarianceMetric
