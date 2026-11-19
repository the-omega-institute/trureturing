/- GID: D5/S1/Recurrence/FiniteTransferSeries
   generality: G
   mirror-B: D5/B/S1/Recurrence/FiniteTransferSeries
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite matrix power series have a formal resolvent with a unit-constant denominator. -/

import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.PowerSeries.Inverse

/-! Scalar observations of finite matrix powers and their exact formal resolvent. -/

open PowerSeries (C X coeff mk constantCoeff)

namespace D5.S1.Recurrence.FiniteTransferSeries

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The shifted series of scalar observations of the powers of a finite matrix. -/
def walks (M : Matrix ι ι ℚ) (u v : ι → ℚ) : PowerSeries ℚ :=
  mk fun
    | 0 => 0
    | n + 1 => dotProduct u ((M ^ n).mulVec v)

private def powerSeries (M : Matrix ι ι ℚ) : Matrix ι ι (PowerSeries ℚ) :=
  fun i j => mk fun n => (M ^ n) i j

private theorem powerSeries_left (M : Matrix ι ι ℚ) :
    (1 - (X : PowerSeries ℚ) • M.map C) * powerSeries M = 1 := by
  rw [sub_mul, one_mul, Matrix.smul_mul]
  ext i j n
  cases n with
  | zero =>
    have h (i j : ι) :
        coeff 0 ((1 : Matrix ι ι (PowerSeries ℚ)) i j) =
          (1 : Matrix ι ι ℚ) i j := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, powerSeries, h]
  | succ n =>
    have h (i j : ι) : coeff (n + 1) ((1 : Matrix ι ι (PowerSeries ℚ)) i j) = 0 := by
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, PowerSeries.coeff_one]
    have hc : coeff (n + 1) (X * ((M.map C) * powerSeries M) i j) =
        (M * M ^ n) i j := by
      rw [PowerSeries.coeff_succ_X_mul]
      simp [Matrix.mul_apply, powerSeries, map_sum, PowerSeries.coeff_C_mul]
    simp [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, powerSeries, h, hc, pow_succ']

private theorem lift_pencil (M : Matrix ι ι ℚ) :
    ((1 - (Polynomial.X : Polynomial ℚ) • M.map (Polynomial.C (R := ℚ)) :
      Matrix ι ι (Polynomial ℚ)).map Polynomial.coeToPowerSeries.ringHom) = 1 - (X : PowerSeries ℚ) • M.map C := by
  change Polynomial.coeToPowerSeries.ringHom.mapMatrix _ = _
  rw [map_sub, map_one]
  congr 1
  apply Matrix.ext
  intro i j
  change Polynomial.coeToPowerSeries.ringHom (Polynomial.X * Polynomial.C (M i j)) =
    X * C (M i j)
  rw [map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X, Polynomial.coe_C]

private theorem pencil_const (M : Matrix ι ι ℚ) :
    (1 - (X : PowerSeries ℚ) • M.map C : Matrix ι ι (PowerSeries ℚ)).map constantCoeff = 1 := by
  change constantCoeff.mapMatrix _ = _
  rw [map_sub, map_one]
  have h : constantCoeff.mapMatrix ((X : PowerSeries ℚ) • M.map C) = 0 := by
    ext i j
    simp [Matrix.smul_apply, smul_eq_mul]
  rw [h, sub_zero]

private theorem walks_eq_sum (M : Matrix ι ι ℚ) (u v : ι → ℚ) :
    walks M u v =
      X * dotProduct (C ∘ u) ((powerSeries M).mulVec (C ∘ v)) := by
  ext (_ | n)
  · simp [walks]
  · rw [PowerSeries.coeff_succ_X_mul]
    simp [walks, dotProduct, Matrix.mulVec, map_sum, powerSeries,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C]

/-- Each coefficient uses the corresponding matrix power. The exact resolvent has a
polynomial denominator with constant coefficient one. -/
theorem walks_resolvent (M : Matrix ι ι ℚ) (u v : ι → ℚ) :
    let A : Matrix ι ι (Polynomial ℚ) :=
      1 - (Polynomial.X : Polynomial ℚ) • M.map (Polynomial.C (R := ℚ))
    let B : Matrix ι ι (PowerSeries ℚ) := 1 - (X : PowerSeries ℚ) • M.map C
    A.det.coeff 0 = 1 ∧
    walks M u v = X * dotProduct (C ∘ u) (B⁻¹.mulVec (C ∘ v)) ∧
    (A.det : PowerSeries ℚ) * walks M u v =
      (↑((Polynomial.X : Polynomial ℚ) * dotProduct (Polynomial.C (R := ℚ) ∘ u)
        (A.adjugate.mulVec (Polynomial.C ∘ v))) : PowerSeries ℚ) := by
  dsimp only
  let A : Matrix ι ι (Polynomial ℚ) :=
      1 - (Polynomial.X : Polynomial ℚ) • M.map (Polynomial.C (R := ℚ))
  let B : Matrix ι ι (PowerSeries ℚ) := 1 - (X : PowerSeries ℚ) • M.map C
  let f : Polynomial ℚ →+* PowerSeries ℚ := Polynomial.coeToPowerSeries.ringHom
  have hAB : f.mapMatrix A = B := lift_pencil M
  have hdet : f A.det = B.det := by rw [f.map_det, hAB]
  have hz : constantCoeff B.det = 1 := by
    rw [RingHom.map_det]
    change (B.map constantCoeff).det = 1
    rw [pencil_const, Matrix.det_one]
  have hzA : A.det.coeff 0 = 1 := by
    rw [← Polynomial.constantCoeff_coe, ← Polynomial.coeToPowerSeries.ringHom_apply]
    exact (congrArg constantCoeff hdet).trans hz
  have hu : IsUnit B.det := PowerSeries.isUnit_iff_constantCoeff.mpr (hz ▸ isUnit_one)
  have hG : powerSeries M = B⁻¹ := by
    calc
      powerSeries M = B⁻¹ * (B * powerSeries M) := by
        rw [← mul_assoc, Matrix.nonsing_inv_mul B hu, one_mul]
      _ = B⁻¹ := by rw [powerSeries_left M, mul_one]
  have hadj : B.det • powerSeries M = (A.adjugate.map f) := by
    change B.det • powerSeries M = f.mapMatrix A.adjugate
    rw [f.map_adjugate, hAB]
    calc
      B.det • powerSeries M = (B.det • (1 : Matrix ι ι (PowerSeries ℚ))) * powerSeries M := by
        rw [Matrix.smul_mul, Matrix.one_mul]
      _ = B.adjugate := by rw [← Matrix.adjugate_mul, mul_assoc, powerSeries_left, mul_one]
  refine ⟨hzA, ?_, ?_⟩
  · rw [walks_eq_sum, hG]
  · change f A.det * walks M u v = f _
    rw [hdet, walks_eq_sum, map_mul]
    have hfX : f (Polynomial.X : Polynomial ℚ) = X := Polynomial.coe_X
    rw [hfX, mul_left_comm]
    congr 1
    rw [f.map_dotProduct]
    have hlift (w : ι → ℚ) : f ∘ (Polynomial.C ∘ w) = C ∘ w := by
      funext i
      exact Polynomial.coe_C (w i)
    have hv : f ∘ A.adjugate.mulVec (Polynomial.C ∘ v) =
        (A.adjugate.map f).mulVec (C ∘ v) := by
      funext i
      simpa only [Function.comp_apply, ← hlift v] using
        f.map_mulVec A.adjugate (Polynomial.C ∘ v) i
    rw [hlift, hv, ← hadj, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

end D5.S1.Recurrence.FiniteTransferSeries
