/- GID: D5/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/LinGProperty/GeometricMeanBound
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [D5/S3/Quantum/Matrix/AlternativeMeanLinearization, D5/S3/Quantum/Matrix/CayleyResolvent]
   utility: none
   digest: Quantitative harmonic lower bounds for the positive matrix geometric mean. -/

import D5.S3.Quantum.Matrix.AlternativeMeanLinearization
import D5.S3.Quantum.Matrix.CayleyResolvent
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

noncomputable section
open Matrix
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
namespace D5.S3.Quantum.Matrix.LinGProperty

variable {n : ℕ}

/-- The geometric mean, through the inverse-base Riccati definition. -/
def geometricMean (P Q : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  AlternativeMeanLinearization.gmInv P⁻¹ Q

/-- The geometric mean is positive definite and solves its Riccati equation. -/
theorem geometricMean_riccati {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    (geometricMean P Q).PosDef ∧ geometricMean P Q * P⁻¹ * geometricMean P Q = Q :=
  AlternativeMeanLinearization.riccati hP.inv hQ

/-- The harmonic mean is dominated by the geometric mean. -/
theorem harmonic_le_geometricMean {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    ((1 / 2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹ ≤ geometricMean P Q := by
  let G := geometricMean P Q
  have hG : G.PosDef := (geometricMean_riccati hP hQ).1
  have hR : G * P⁻¹ * G = Q := (geometricMean_riccati hP hQ).2
  letI := hP.isUnit.invertible
  letI := hQ.isUnit.invertible
  letI := hG.isUnit.invertible
  have hRi : G⁻¹ * P * G⁻¹ = Q⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [← hR]
    simp [mul_assoc]
  have hRi' : G⁻¹ * (P * G⁻¹) = Q⁻¹ := by simpa only [mul_assoc] using hRi
  have hpos : 0 ≤ (G⁻¹ - P⁻¹) * P * (G⁻¹ - P⁻¹) :=
    (hG.inv.isHermitian.sub hP.inv.isHermitian).isSelfAdjoint.conjugate_nonneg hP.posSemidef.nonneg
  have he : (G⁻¹ - P⁻¹) * P * (G⁻¹ - P⁻¹) = Q⁻¹ + P⁻¹ - (2 : ℝ) • G⁻¹ := by
    simp only [sub_mul, mul_sub]
    simp only [mul_assoc, Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible,
      mul_one, one_mul, hRi']
    module
  rw [he] at hpos
  have horder : G⁻¹ ≤ (1 / 2 : ℝ) • (P⁻¹ + Q⁻¹) := by
    have hh := smul_le_smul_of_nonneg_left (sub_nonneg.mp hpos) (by norm_num : (0 : ℝ) ≤ 1/2)
    convert hh using 1 <;> module
  have hi := CayleyResolvent.inverse_antitone hG.inv ((hP.inv.add hQ.inv).smul (by norm_num : (0 : ℝ) < 1/2)) horder
  simpa using hi

/-- The harmonic mean equals the arithmetic mean minus its noncommutative correction. -/
theorem harmonic_eq_arithmetic_correction {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) :
    ((1 / 2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹ =
      (1 / 2 : ℝ) • (P + Q) -
        ((1 / 2 : ℝ) • (P - Q)) * ((1 / 2 : ℝ) • (P + Q))⁻¹ *
          ((1 / 2 : ℝ) • (P - Q)) := by
  let H := (1 / 2 : ℝ) • (P + Q)
  let K := (1 / 2 : ℝ) • (P - Q)
  have hH : H.PosDef := (hP.add hQ).smul (by norm_num : (0 : ℝ) < 1/2)
  letI := hP.isUnit.invertible
  letI := hQ.isUnit.invertible
  letI := hH.isUnit.invertible
  have hS : (1 / 2 : ℝ) • (P⁻¹ + Q⁻¹) = Q⁻¹ * H * P⁻¹ := by
    dsimp [H]
    simp only [mul_smul_comm, smul_mul_assoc, mul_add, add_mul, mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible, mul_one, one_mul]
    module
  have hh : ((1 / 2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹ = P * H⁻¹ * Q := by
    apply Matrix.inv_eq_right_inv
    rw [hS]
    simp [mul_assoc]
  have hP' : P = H + K := by dsimp [H, K]; module
  have hQ' : Q = H - K := by dsimp [H, K]; module
  change _ = H - K * H⁻¹ * K
  rw [hh, hP', hQ']
  simp only [add_mul, sub_mul, mul_add, mul_sub, mul_assoc,
    Matrix.inv_mul_of_invertible, Matrix.mul_inv_of_invertible, one_mul, mul_one]
  abel

/-- A square bound on the half-difference yields a quantitative lower bound on the mean. -/
theorem arithmetic_sub_le_geometricMean {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) {c d : ℝ} (hc : 0 < c)
    (hfloor : c • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ (1 / 2 : ℝ) • (P + Q))
    (hsquare : ((1 / 2 : ℝ) • (P - Q)) * ((1 / 2 : ℝ) • (P - Q)) ≤
      d • (1 : Matrix (Fin n) (Fin n) ℂ)) :
    (1 / 2 : ℝ) • (P + Q) - (d / c) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
      geometricMean P Q := by
  let H := (1 / 2 : ℝ) • (P + Q)
  let K := (1 / 2 : ℝ) • (P - Q)
  have hH : H.PosDef := (hP.add hQ).smul (by norm_num : (0 : ℝ) < 1/2)
  have hK : K.IsHermitian := (hP.isHermitian.sub hQ.isHermitian).smul (by simp)
  have hiscalar : (c • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = (1 / c : ℝ) • 1 := by
    apply Matrix.inv_eq_right_inv
    simp [smul_mul_smul, hc.ne']
  have hi : H⁻¹ ≤ (1 / c : ℝ) • 1 := by
    rw [← hiscalar]
    exact CayleyResolvent.inverse_antitone (Matrix.PosDef.one.smul hc) hH hfloor
  have hk : K * H⁻¹ * K ≤ (d / c) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    calc
      K * H⁻¹ * K ≤ K * ((1 / c : ℝ) • 1) * K := hK.isSelfAdjoint.conjugate_le_conjugate hi
      _ = (1 / c : ℝ) • (K * K) := by simp [mul_smul_comm, smul_mul_assoc]
      _ ≤ (1 / c : ℝ) • (d • (1 : Matrix (Fin n) (Fin n) ℂ)) :=
        smul_le_smul_of_nonneg_left hsquare (by positivity)
      _ = (d / c) • 1 := by rw [smul_smul]; congr 1; ring
  calc
    H - (d / c) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ H - K * H⁻¹ * K := sub_le_sub_left hk H
    _ = ((1 / 2 : ℝ) • (P⁻¹ + Q⁻¹))⁻¹ := (harmonic_eq_arithmetic_correction hP hQ).symm
    _ ≤ geometricMean P Q := harmonic_le_geometricMean hP hQ

/-- Positive scaling in both inputs scales the mean by the geometric scalar factor. -/
theorem geometricMean_smul {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P.PosDef) (hQ : Q.PosDef) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    geometricMean (r • P) (s • Q) = Real.sqrt (r * s) • geometricMean P Q := by
  let G := geometricMean P Q
  have hG : G.PosDef := (geometricMean_riccati hP hQ).1
  have hR : G * P⁻¹ * G = Q := (geometricMean_riccati hP hQ).2
  letI := hP.isUnit.invertible
  have his : (r • P)⁻¹ = r⁻¹ • P⁻¹ := by
    apply Matrix.inv_eq_right_inv
    simp [smul_mul_smul, hr.ne']
  have hk : 0 < Real.sqrt (r * s) := Real.sqrt_pos.mpr (mul_pos hr hs)
  have hcoeff : Real.sqrt (r*s) * r⁻¹ * Real.sqrt (r*s) = s := by
    calc
      _ = (Real.sqrt (r*s) * Real.sqrt (r*s)) / r := by ring
      _ = (r*s) / r := by rw [Real.mul_self_sqrt (mul_pos hr hs).le]
      _ = s := by field_simp
  apply AlternativeMeanLinearization.riccati_unique (hP.smul hr).inv (hG.smul hk)
  rw [his]
  simp only [smul_mul_smul, hR, hcoeff]

/-- A zero second input has zero geometric mean. -/
@[simp] theorem geometricMean_zero_right (P : Matrix (Fin n) (Fin n) ℂ) :
    geometricMean P 0 = 0 := by
  simp [geometricMean, AlternativeMeanLinearization.gmInv, Real.zero_rpow]

/-- A zero first input has zero geometric mean. -/
@[simp] theorem geometricMean_zero_left (Q : Matrix (Fin n) (Fin n) ℂ) :
    geometricMean 0 Q = 0 := by
  simp [geometricMean, AlternativeMeanLinearization.gmInv, Real.zero_rpow]

end D5.S3.Quantum.Matrix.LinGProperty
