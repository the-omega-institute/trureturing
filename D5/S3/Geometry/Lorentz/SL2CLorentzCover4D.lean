/- GID: D5/S3/Geometry/Lorentz/SL2CLorentzCover4D
   generality: G
   mirror-B: D5/B/S3/Geometry/Lorentz/SL2CLorentzCover4D
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Pauli spinor conjugation, the proper Lorentz double cover and the celestial Möbius action. -/

import OmegaBuild.Commands
import D5.S3.Geometry.SU2EulerCover
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! The Pauli coordinates use the time-positive signature and the spinor action
by conjugation with the Hermitian adjoint. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped Matrix ComplexConjugate

namespace D5.S3.Geometry.Lorentz.SL2CLorentzCover4D

abbrev V4 := Fin 4 → ℝ
abbrev H2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

open OmegaMath.SU2EulerCover

def eta : Matrix (Fin 4) (Fin 4) ℝ := diagonal ![1, -1, -1, -1]

def minkowskiNormSq (x : V4) : ℝ :=
  x 0 ^ 2 - (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)

def IsProperOrthochronous (L : Matrix (Fin 4) (Fin 4) ℝ) : Prop :=
  Lᵀ * eta * L = eta ∧ L.det = 1 ∧ 0 < L 0 0

def pauliHerm (x : V4) : H2 :=
  !![(x 0 : ℂ) + x 3, (x 1 : ℂ) - Complex.I * x 2;
     (x 1 : ℂ) + Complex.I * x 2, (x 0 : ℂ) - x 3]

def minkowski_from_pauliHerm (M : H2) : V4 :=
  ![((M 0 0).re + (M 1 1).re) / 2, (M 0 1).re, -(M 0 1).im,
     ((M 0 0).re - (M 1 1).re) / 2]

theorem pauliHerm_isHermitian (x : V4) : (pauliHerm x).IsHermitian := by
  apply IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [pauliHerm, sub_eq_add_neg]

theorem pauliHerm_minkowski_inverse (x : V4) :
    minkowski_from_pauliHerm (pauliHerm x) = x := by
  funext i
  fin_cases i <;>
    simp [minkowski_from_pauliHerm, pauliHerm, Complex.mul_re, Complex.mul_im]

theorem minkowski_pauliHerm_inverse (M : H2) (hM : M.IsHermitian) :
    pauliHerm (minkowski_from_pauliHerm M) = M := by
  have h00 : (M 0 0).im = 0 := by
    have h := congrArg Complex.im (hM.apply 0 0)
    simp at h
    linarith
  have h11 : (M 1 1).im = 0 := by
    have h := congrArg Complex.im (hM.apply 1 1)
    simp at h
    linarith
  have hre := congrArg Complex.re (hM.apply 1 0)
  have him := congrArg Complex.im (hM.apply 1 0)
  simp at hre him
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    apply Complex.ext <;>
      simp [pauliHerm, minkowski_from_pauliHerm, Complex.mul_re, Complex.mul_im, h00, h11, ← hre, ← him]
  all_goals ring

theorem pauliHerm_det (x : V4) :
    (pauliHerm x).det = (minkowskiNormSq x : ℂ) := by
  rw [Matrix.det_fin_two]
  apply Complex.ext <;>
    simp [pauliHerm, minkowskiNormSq, Complex.mul_re, Complex.mul_im, pow_two] <;> ring

theorem pauliHerm_trace (x : V4) :
    (pauliHerm x).trace = (2 * x 0 : ℂ) := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, pauliHerm]
  ring

private theorem pauliHerm_injective : Function.Injective pauliHerm :=
  Function.LeftInverse.injective pauliHerm_minkowski_inverse

private def timeAxis : V4 := Pi.single 0 1

private theorem pauliHerm_timeAxis : pauliHerm timeAxis = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliHerm, timeAxis, Pi.single_apply, Matrix.one_apply]

def lorentzVec (A : SL2C) (x : V4) : V4 :=
  minkowski_from_pauliHerm ((A : H2) * pauliHerm x * (A : H2)ᴴ)

def lorentzOfSL2C (A : SL2C) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of fun i j => lorentzVec A (Pi.single j 1) i

private def lorentzLinear (A : SL2C) : V4 →ₗ[ℝ] V4 where
  toFun := lorentzVec A
  map_add' x y := by
    have hpauli : pauliHerm (x + y) = pauliHerm x + pauliHerm y := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliHerm, Pi.add_apply] <;> ring
    funext i
    fin_cases i <;>
      simp [lorentzVec, hpauli, Matrix.mul_add, Matrix.add_mul,
        minkowski_from_pauliHerm, Complex.add_re, Complex.add_im] <;> ring
  map_smul' r x := by
    have hpauli : pauliHerm (r • x) = (r : ℂ) • pauliHerm x := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [pauliHerm, Pi.smul_apply, smul_eq_mul] <;> ring
    funext i
    fin_cases i <;>
      simp [lorentzVec, hpauli, minkowski_from_pauliHerm,
        Complex.mul_re, Complex.mul_im, smul_eq_mul] <;> ring

theorem pauliHerm_lorentzVec (A : SL2C) (x : V4) :
    pauliHerm (lorentzVec A x) = (A : H2) * pauliHerm x * (A : H2)ᴴ := by
  apply minkowski_pauliHerm_inverse
  simpa [Matrix.mul_assoc] using
    Matrix.isHermitian_conjTranspose_mul_mul (A : H2)ᴴ (pauliHerm_isHermitian x)

theorem lorentzOfSL2C_mulVec (A : SL2C) (x : V4) :
    lorentzOfSL2C A *ᵥ x = lorentzVec A x := by
  exact LinearMap.toMatrix'_mulVec (lorentzLinear A) x

theorem lorentzOfSL2C_one : lorentzOfSL2C 1 = 1 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [lorentzOfSL2C_mulVec, Matrix.one_mulVec]
  simp [lorentzVec, Matrix.SpecialLinearGroup.coe_one, pauliHerm_minkowski_inverse]

theorem lorentzOfSL2C_mul (A B : SL2C) :
    lorentzOfSL2C (A * B) = lorentzOfSL2C A * lorentzOfSL2C B := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec]
  simp only [lorentzOfSL2C_mulVec]
  apply pauliHerm_injective
  simp [pauliHerm_lorentzVec, Matrix.mul_assoc]

theorem lorentzOfSL2C_preserves_norm (A : SL2C) (x : V4) :
    minkowskiNormSq (lorentzOfSL2C A *ᵥ x) = minkowskiNormSq x := by
  apply Complex.ofReal_injective
  simp [lorentzOfSL2C_mulVec, ← pauliHerm_det, pauliHerm_lorentzVec,
    Matrix.det_mul, Matrix.det_conjTranspose]

private theorem metric_polarization (x y : V4) :
    2 * (x ⬝ᵥ (eta *ᵥ y)) =
      minkowskiNormSq (x + y) - minkowskiNormSq x - minkowskiNormSq y := by
  simp [eta, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four, minkowskiNormSq]
  ring

private theorem metric_mulVec (L : Matrix (Fin 4) (Fin 4) ℝ) (x y : V4) :
    (L *ᵥ x) ⬝ᵥ (eta *ᵥ (L *ᵥ y)) = x ⬝ᵥ ((Lᵀ * eta * L) *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

theorem lorentzOfSL2C_preserves_minkowski (A : SL2C) :
    (lorentzOfSL2C A)ᵀ * eta * lorentzOfSL2C A = eta := by
  let L := lorentzOfSL2C A
  have h (x y : V4) : x ⬝ᵥ ((Lᵀ * eta * L) *ᵥ y) = x ⬝ᵥ (eta *ᵥ y) := by
    rw [← metric_mulVec]
    have hp := metric_polarization (L *ᵥ x) (L *ᵥ y)
    rw [← Matrix.mulVec_add, lorentzOfSL2C_preserves_norm, lorentzOfSL2C_preserves_norm,
      lorentzOfSL2C_preserves_norm, ← metric_polarization] at hp
    linarith
  ext i j
  simpa [Matrix.mulVec_single_one, single_dotProduct] using
    h (Pi.single i 1) (Pi.single j 1)

theorem lorentzOfSL2C_orthochronous (A : SL2C) : 1 ≤ lorentzOfSL2C A 0 0 := by
  let M : H2 := A
  have ht : lorentzOfSL2C A 0 0 =
      (‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) / 2 := by
    change lorentzVec A timeAxis 0 = _
    simp [lorentzVec, pauliHerm_timeAxis, minkowski_from_pauliHerm, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply, Complex.mul_re,
      Complex.sq_norm, Complex.normSq_apply, M]
    ring
  have hd : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    exact Matrix.det_fin_two M ▸ A.det_coe
  have hn := norm_sub_le (M 0 0 * M 1 1) (M 0 1 * M 1 0)
  rw [hd, norm_one, norm_mul, norm_mul] at hn
  rw [ht]
  nlinarith only [hn, sq_nonneg (‖M 0 0‖ - ‖M 1 1‖), sq_nonneg (‖M 0 1‖ - ‖M 1 0‖)]

open scoped ComplexOrder in
theorem sl2c_gram_properties (A : SL2C) :
    ((A : H2) * (A : H2)ᴴ).PosDef ∧ ((A : H2) * (A : H2)ᴴ).det = 1 ∧
      2 ≤ ((A : H2) * (A : H2)ᴴ).trace.re := by
  have hA : IsUnit (A : H2) := (Matrix.isUnit_iff_isUnit_det _).2 (by simp)
  have htrace := congrArg (fun M : H2 => M.trace.re) (pauliHerm_lorentzVec A timeAxis)
  simp [pauliHerm_trace, pauliHerm_timeAxis] at htrace
  refine ⟨Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_of_isUnit hA),
    by simp [Matrix.det_mul, Matrix.det_conjTranspose], ?_⟩
  rw [← htrace]
  change 2 ≤ 2 * lorentzOfSL2C A 0 0
  linarith [lorentzOfSL2C_orthochronous A]

private theorem lorentzOfSL2C_neg (A : SL2C) : lorentzOfSL2C (-A) = lorentzOfSL2C A := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  simp [lorentzOfSL2C_mulVec, lorentzVec, Matrix.SpecialLinearGroup.coe_neg]

theorem lorentzOfSL2C_ker_iff (A : SL2C) :
    lorentzOfSL2C A = 1 ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro h
    let M : H2 := A
    have hfix (x : V4) : M * pauliHerm x * Mᴴ = pauliHerm x := by
      rw [← pauliHerm_lorentzVec, ← lorentzOfSL2C_mulVec, h, Matrix.one_mulVec]
    have hunit : M * Mᴴ = 1 := by simpa [pauliHerm_timeAxis] using hfix timeAxis
    have hunit' := mul_eq_one_comm.mp hunit
    have hcomm (x : V4) : M * pauliHerm x = pauliHerm x * M := by
      calc
        M * pauliHerm x = (M * pauliHerm x * Mᴴ) * M := by
          rw [Matrix.mul_assoc, hunit', Matrix.mul_one]
        _ = _ := by rw [hfix]
    have h01 := congrArg (fun N : H2 => N 0 1) (hcomm ![0, 0, 0, 1])
    have h10 := congrArg (fun N : H2 => N 1 0) (hcomm ![0, 0, 0, 1])
    have hd := congrArg (fun N : H2 => N 0 1) (hcomm ![0, 1, 0, 0])
    simp [pauliHerm, Matrix.mul_apply, Fin.sum_univ_two] at h01 h10 hd
    have hz01 : M 0 1 = 0 := by linear_combination -h01 / 2
    have hz10 : M 1 0 = 0 := by linear_combination h10 / 2
    have hs : M 0 0 * M 0 0 = 1 := by
      have h := (Matrix.det_fin_two M).symm.trans A.det_coe
      simpa [← hd, hz01, hz10] using h
    have hp : (M 0 0 - 1) * (M 0 0 + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hp with hp | hp
    · left
      have h00 := sub_eq_zero.mp hp
      apply Subtype.ext
      change M = 1
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz01, hz10, ← hd, h00]
    · right
      have h00 : M 0 0 = -1 := by linear_combination hp
      apply Subtype.ext
      change M = ((-1 : SL2C) : H2)
      rw [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hz01, hz10, ← hd, h00]
  · rintro (rfl | rfl)
    · exact lorentzOfSL2C_one
    · rw [lorentzOfSL2C_neg, lorentzOfSL2C_one]

theorem lorentzOfSL2C_eq_iff (A B : SL2C) :
    lorentzOfSL2C A = lorentzOfSL2C B ↔ A = B ∨ A = -B := by
  constructor
  · intro h
    have hker : lorentzOfSL2C (B⁻¹ * A) = 1 := by
      rw [lorentzOfSL2C_mul, h, ← lorentzOfSL2C_mul, inv_mul_cancel, lorentzOfSL2C_one]
    rcases (lorentzOfSL2C_ker_iff _).mp hker with h₁ | h₂
    · left
      simpa [← mul_assoc] using congrArg (B * ·) h₁
    · right
      simpa [← mul_assoc] using congrArg (B * ·) h₂
  · rintro (rfl | rfl)
    · rfl
    · exact lorentzOfSL2C_neg B

private def spatialBlock (L : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  L.submatrix Fin.succ Fin.succ

private def spatialLift (R : Matrix (Fin 3) (Fin 3) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (vecCons ![1, 0, 0, 0] fun i => vecCons 0 (R i))

private theorem spatialLift_mulVec (R : Matrix (Fin 3) (Fin 3) ℝ) (x : V4) :
    spatialLift R *ᵥ x = vecCons (x 0) (R *ᵥ (x ∘ Fin.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i <;>
    simp [spatialLift, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

private theorem spatialLift_mul (R S : Matrix (Fin 3) (Fin 3) ℝ) :
    spatialLift (R * S) = spatialLift R * spatialLift S := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, spatialLift_mulVec, spatialLift_mulVec, spatialLift_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

private theorem spatialLift_det (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (spatialLift R).det = R.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hz (i : Fin 3) : (![0, 0, 0] : Fin 3 → ℝ) i = 0 := by fin_cases i <;> rfl
  simp [spatialLift, hz]
  congr 1

private theorem metric_self (x : V4) : x ⬝ᵥ (eta *ᵥ x) = minkowskiNormSq x := by
  simp [eta, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_four, minkowskiNormSq]
  ring

private theorem metric_preserves_norm {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : Lᵀ * eta * L = eta) (x : V4) :
    minkowskiNormSq (L *ᵥ x) = minkowskiNormSq x := by
  rw [← metric_self, metric_mulVec, hL, metric_self]

private theorem rest_frame_block {L : Matrix (Fin 4) (Fin 4) ℝ}
    (hL : Lᵀ * eta * L = eta) (hdet : L.det = 1) (hfix : L *ᵥ timeAxis = timeAxis) :
    L = spatialLift (spatialBlock L) ∧ (spatialBlock L)ᵀ * spatialBlock L = 1 ∧
      (spatialBlock L).det = 1 := by
  have hcol (i : Fin 4) : L i 0 = timeAxis i := by
    simpa [timeAxis, Matrix.mulVec_single_one] using congrFun hfix i
  have hrow (j : Fin 3) : L 0 j.succ = 0 := by
    have hp := metric_mulVec L timeAxis (Pi.single j.succ 1)
    rw [hfix, hL] at hp
    simpa [timeAxis, eta, Matrix.mulVec_diagonal, single_dotProduct, Matrix.mulVec_single_one] using hp
  have hblock : L = spatialLift (spatialBlock L) := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · exact Fin.cases (by simp [hcol, timeAxis, spatialLift])
        (fun j => by rw [hrow]; fin_cases j <;> rfl) j
    · exact Fin.cases (by simp [hcol, timeAxis, spatialLift]) (fun _ => rfl) j
  refine ⟨hblock, ?_, ?_⟩
  · ext i j
    have hp := congrArg (fun M : Matrix (Fin 4) (Fin 4) ℝ => M i.succ j.succ) hL
    change (Lᵀ * eta * L) i.succ j.succ = eta i.succ j.succ at hp
    rw [Matrix.mul_apply, Fin.sum_univ_succ] at hp
    have hsign (k : Fin 3) : (![1, -1, -1, -1] : V4) k.succ = -1 := by
      fin_cases k <;> rfl
    simp [eta, Matrix.mul_diagonal, hrow, hsign, Matrix.diagonal_apply] at hp
    have hn := congrArg Neg.neg hp
    by_cases h : i = j <;>
      simpa [spatialBlock, Matrix.mul_apply, Matrix.one_apply, h, ← Finset.sum_neg_distrib] using hn
  · rw [hblock, spatialLift_det] at hdet
    exact hdet

private theorem diagonal_sandwich (p q : ℂ) (M : H2) :
    !![p, 0; 0, q] * M * (!![p, 0; 0, q] : H2)ᴴ =
      !![p * conj p * M 0 0, p * conj q * M 0 1;
         q * conj p * M 1 0, q * conj q * M 1 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;> ring

theorem lorentzOfSL2C_rotZ (θ : ℝ) :
    lorentzOfSL2C (rotZ θ) =
      !![1, 0, 0, 0; 0, Real.cos θ, -Real.sin θ, 0;
         0, Real.sin θ, Real.cos θ, 0; 0, 0, 0, 1] := by
  let phase (a : ℝ) := Complex.exp ((a : ℂ) * Complex.I)
  have hc (a : ℝ) : conj (phase a) = phase (-a) := by
    simp [phase, ← Complex.exp_conj, mul_neg, neg_mul]
  have hp (a b : ℝ) : phase a * phase b = phase (a + b) := by
    simp [phase, add_mul, Complex.exp_add]
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [lorentzOfSL2C_mulVec]
  unfold lorentzVec
  rw [coe_rotZ]
  change minkowski_from_pauliHerm (!![phase (-θ / 2), 0; 0, phase (θ / 2)] * pauliHerm x *
    (!![phase (-θ / 2), 0; 0, phase (θ / 2)] : H2)ᴴ) = _
  rw [diagonal_sandwich]
  simp only [hc, hp, show -θ / 2 + -(θ / 2) = -θ by ring,
    show -θ / 2 + -(-θ / 2) = 0 by ring, show θ / 2 + -(θ / 2) = 0 by ring]
  funext i
  fin_cases i <;>
    simp [phase, Complex.exp_mul_I, Complex.mul_re, Complex.mul_im,
      minkowski_from_pauliHerm, pauliHerm, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  all_goals ring

theorem lorentzOfSL2C_rotY (φ : ℝ) :
    lorentzOfSL2C (rotY φ) =
      !![1, 0, 0, 0; 0, Real.cos φ, 0, Real.sin φ;
         0, 0, 1, 0; 0, -Real.sin φ, 0, Real.cos φ] := by
  have hcos : Real.cos φ = Real.cos (φ / 2) ^ 2 - Real.sin (φ / 2) ^ 2 := by
    simpa only [show 2 * (φ / 2) = φ by ring] using Real.cos_two_mul' (φ / 2)
  have hsin : Real.sin φ = 2 * Real.sin (φ / 2) * Real.cos (φ / 2) := by
    simpa only [show 2 * (φ / 2) = φ by ring] using Real.sin_two_mul (φ / 2)
  have hnorm := Real.sin_sq_add_cos_sq (φ / 2)
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [lorentzOfSL2C_mulVec]
  unfold lorentzVec
  rw [coe_rotY]
  funext i
  fin_cases i <;>
    simp [minkowski_from_pauliHerm, pauliHerm, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.mulVec, dotProduct, Fin.sum_univ_four, Complex.mul_re, Complex.mul_im,
      -Complex.ofReal_sin, -Complex.ofReal_cos, hcos, hsin]
  · linear_combination x 0 * hnorm
  · ring
  · linear_combination x 2 * hnorm
  · ring

theorem lorentzOfSL2C_boostZ (η : ℝ) :
    lorentzOfSL2C (boostZ η) =
      !![Real.cosh η, 0, 0, Real.sinh η; 0, 1, 0, 0;
         0, 0, 1, 0; Real.sinh η, 0, 0, Real.cosh η] := by
  have hexp (a b : ℝ) : (Real.exp a : ℂ) * (Real.exp b : ℂ) = (Real.exp (a + b) : ℂ) := by
    rw [Real.exp_add, Complex.ofReal_mul]
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [lorentzOfSL2C_mulVec]
  unfold lorentzVec
  rw [coe_boostZ, diagonal_sandwich]
  simp only [Complex.conj_ofReal, hexp, show η / 2 + η / 2 = η by ring,
    show η / 2 + -η / 2 = 0 by ring, show -η / 2 + η / 2 = 0 by ring,
    show -η / 2 + -η / 2 = -η by ring, Real.exp_zero]
  funext i
  fin_cases i <;>
    simp [minkowski_from_pauliHerm, pauliHerm, Matrix.mulVec, dotProduct,
      Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_re, -Complex.ofReal_neg, Real.cosh_eq, Real.sinh_eq,
      Fin.sum_univ_four] <;> ring

private theorem rotZ_lift (θ : ℝ) : lorentzOfSL2C (rotZ θ) = spatialLift (rotZ3 θ) := by
  rw [lorentzOfSL2C_rotZ]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private theorem rotY_lift (φ : ℝ) : lorentzOfSL2C (rotY φ) = spatialLift (rotY3 φ) := by
  rw [lorentzOfSL2C_rotY]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem lorentzOfSL2C_rotZ_det (θ : ℝ) : (lorentzOfSL2C (rotZ θ)).det = 1 := by
  rw [rotZ_lift, spatialLift_det, rotZ3_det]

theorem lorentzOfSL2C_rotY_det (φ : ℝ) : (lorentzOfSL2C (rotY φ)).det = 1 := by
  rw [rotY_lift, spatialLift_det, rotY3_det]

theorem lorentzOfSL2C_boostZ_det (η : ℝ) : (lorentzOfSL2C (boostZ η)).det = 1 := by
  let e : Fin 2 ⊕ Fin 2 ≃ Fin 4 := finSumFinEquiv.trans (Equiv.swap 1 3)
  rw [← Matrix.det_submatrix_equiv_self e, lorentzOfSL2C_boostZ]
  have h : (!![Real.cosh η, 0, 0, Real.sinh η; 0, 1, 0, 0;
        0, 0, 1, 0; Real.sinh η, 0, 0, Real.cosh η] : Matrix (Fin 4) (Fin 4) ℝ).submatrix e e =
      fromBlocks !![Real.cosh η, Real.sinh η; Real.sinh η, Real.cosh η] 0 0 1 := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      fin_cases i <;> fin_cases j <;> rfl
  rw [h, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one, Matrix.det_fin_two_of,
    ← sq, ← sq, Real.cosh_sq_sub_sinh_sq]

private theorem unitary_mul {U V : SL2C} (hU : (U : H2)ᴴ * (U : H2) = 1)
    (hV : (V : H2)ᴴ * (V : H2) = 1) : ((U * V : SL2C) : H2)ᴴ * ((U * V : SL2C) : H2) = 1 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc (U : H2)ᴴ, hU, Matrix.one_mul, hV]

private theorem su2_lorentz_det (U : SL2C) (hU : (U : H2)ᴴ * (U : H2) = 1) :
    (lorentzOfSL2C U).det = 1 := by
  obtain ⟨α, β, γ, rfl⟩ := su2_euler U hU
  simp [lorentzOfSL2C_mul, Matrix.det_mul, lorentzOfSL2C_rotY_det, lorentzOfSL2C_rotZ_det]

theorem so3_spinor_lift (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1)
    (hd : R.det = 1) :
    ∃ U : SL2C, (U : H2)ᴴ * (U : H2) = 1 ∧
      (lorentzOfSL2C U).submatrix Fin.succ Fin.succ = R := by
  obtain ⟨α, β, γ, rfl⟩ := so3_euler R hR hd
  refine ⟨rotZ α * rotY β * rotZ γ, ?_, ?_⟩
  · exact unitary_mul (unitary_mul (rotZ_unitary α) (rotY_unitary β)) (rotZ_unitary γ)
  · rw [lorentzOfSL2C_mul, lorentzOfSL2C_mul, rotZ_lift, rotY_lift, rotZ_lift,
      ← spatialLift_mul, ← spatialLift_mul]
    ext i j
    simp [spatialLift]

private theorem lift_rest_rotation (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : Rᵀ * R = 1)
    (hd : R.det = 1) : ∃ U : SL2C, lorentzOfSL2C U = spatialLift R := by
  obtain ⟨U, hU, hblock⟩ := so3_spinor_lift R hR hd
  have hfix : lorentzOfSL2C U *ᵥ timeAxis = timeAxis := by
    rw [lorentzOfSL2C_mulVec, lorentzVec, pauliHerm_timeAxis, Matrix.mul_one,
      mul_eq_one_comm.mp hU, ← pauliHerm_timeAxis, pauliHerm_minkowski_inverse]
  obtain ⟨heq, _⟩ := rest_frame_block (lorentzOfSL2C_preserves_minkowski U) (su2_lorentz_det U hU) hfix
  exact ⟨U, heq.trans (congrArg spatialLift hblock)⟩

private theorem future_unit_to_rest (x : V4) (ht : 0 < x 0) (hx : minkowskiNormSq x = 1) :
    ∃ U : SL2C, ∃ η : ℝ, (U : H2)ᴴ * (U : H2) = 1 ∧
      lorentzOfSL2C (boostZ (-η) * U) *ᵥ x = timeAxis := by
  let r := Real.sqrt (x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2)
  let η := Real.log (x 0 + r)
  obtain ⟨α, β, halign⟩ := align_spatial (x ∘ Fin.succ)
  have hU : lorentzOfSL2C (rotY β * rotZ α) *ᵥ x = ![x 0, 0, 0, r] := by
    rw [lorentzOfSL2C_mul, rotY_lift, rotZ_lift, ← spatialLift_mul, spatialLift_mulVec, halign]
    rfl
  have hr : r ^ 2 = x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 := Real.sq_sqrt (by positivity)
  have hpos : 0 < x 0 + r := add_pos_of_pos_of_nonneg ht (Real.sqrt_nonneg _)
  have hunit : x 0 ^ 2 - r ^ 2 = 1 := by rwa [hr]
  have hinv : (x 0 + r)⁻¹ = x 0 - r := by
    field_simp [hpos.ne']
    linear_combination -hunit
  have hcos : Real.cosh η = x 0 := by
    change Real.cosh (Real.log (x 0 + r)) = x 0
    rw [Real.cosh_log hpos, hinv]
    ring
  have hsin : Real.sinh η = r := by
    change Real.sinh (Real.log (x 0 + r)) = r
    rw [Real.sinh_log hpos, hinv]
    ring
  refine ⟨rotY β * rotZ α, η, unitary_mul (rotY_unitary β) (rotZ_unitary α), ?_⟩
  rw [lorentzOfSL2C_mul, ← Matrix.mulVec_mulVec, hU, lorentzOfSL2C_boostZ,
    Real.cosh_neg, Real.sinh_neg, hcos, hsin]
  funext i
  fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four, timeAxis, Pi.single_apply]
  · linear_combination hunit
  · ring

/-- Extract the spatial rotation and rapidity from the image of the time axis. -/
theorem sl2c_cartan_factorization (A : SL2C) :
    ∃ U V : SL2C, ∃ η : ℝ, (U : H2)ᴴ * (U : H2) = 1 ∧
      (V : H2)ᴴ * (V : H2) = 1 ∧ A = U⁻¹ * boostZ η * V := by
  have ht : 0 < (lorentzOfSL2C A *ᵥ timeAxis) 0 := by
    simpa [timeAxis, Matrix.mulVec_single_one] using
      (lt_of_lt_of_le zero_lt_one (lorentzOfSL2C_orthochronous A))
  have hn : minkowskiNormSq (lorentzOfSL2C A *ᵥ timeAxis) = 1 := by
    rw [lorentzOfSL2C_preserves_norm]
    norm_num [minkowskiNormSq, timeAxis, Pi.single_apply]
  obtain ⟨U, η, hU, hrest⟩ := future_unit_to_rest _ ht hn
  let V := (boostZ (-η) * U) * A
  have hV : lorentzVec V timeAxis = timeAxis := by
    rw [← lorentzOfSL2C_mulVec]
    dsimp only [V]
    rw [lorentzOfSL2C_mul, ← Matrix.mulVec_mulVec, hrest]
  have hVV : (V : H2) * (V : H2)ᴴ = 1 := by
    simpa [pauliHerm_lorentzVec, pauliHerm_timeAxis] using congrArg pauliHerm hV
  refine ⟨U, V, η, hU, mul_eq_one_comm.mp hVV, ?_⟩
  calc
    A = (boostZ (-η) * U)⁻¹ * V := (inv_mul_cancel_left _ _).symm
    _ = U⁻¹ * boostZ η * V := by rw [_root_.mul_inv_rev, boostZ_neg, inv_inv]

theorem lorentzOfSL2C_det_one (A : SL2C) : (lorentzOfSL2C A).det = 1 := by
  obtain ⟨U, V, η, hU, hV, rfl⟩ := sl2c_cartan_factorization A
  have hinv : (lorentzOfSL2C U⁻¹).det = 1 := by
    have h : lorentzOfSL2C U⁻¹ * lorentzOfSL2C U = 1 := by
      rw [← lorentzOfSL2C_mul, inv_mul_cancel, lorentzOfSL2C_one]
    simpa [Matrix.det_mul, su2_lorentz_det U hU] using congrArg Matrix.det h
  simp [lorentzOfSL2C_mul, Matrix.det_mul, hinv, lorentzOfSL2C_boostZ_det, su2_lorentz_det V hV]

theorem lorentzOfSL2C_isProperOrthochronous (A : SL2C) :
    IsProperOrthochronous (lorentzOfSL2C A) :=
  ⟨lorentzOfSL2C_preserves_minkowski A, lorentzOfSL2C_det_one A,
    lt_of_lt_of_le zero_lt_one (lorentzOfSL2C_orthochronous A)⟩

theorem lorentzOfSL2C_surjective (L : Matrix (Fin 4) (Fin 4) ℝ) (hL : IsProperOrthochronous L) :
    ∃ A : SL2C, lorentzOfSL2C A = L := by
  obtain ⟨hmetric, hdet, ht⟩ := hL
  have htime : 0 < (L *ᵥ timeAxis) 0 := by
    simpa [timeAxis, Matrix.mulVec_single_one] using ht
  have hnorm : minkowskiNormSq (L *ᵥ timeAxis) = 1 := by
    rw [metric_preserves_norm hmetric]
    norm_num [minkowskiNormSq, timeAxis, Pi.single_apply]
  obtain ⟨U, η, _, hrest⟩ := future_unit_to_rest _ htime hnorm
  let C := boostZ (-η) * U
  let M := lorentzOfSL2C C * L
  have hfix : M *ᵥ timeAxis = timeAxis := by simpa [M, C, ← Matrix.mulVec_mulVec] using hrest
  have hM : Mᵀ * eta * M = eta := by
    have h := congrArg (fun N => Lᵀ * N * L) (lorentzOfSL2C_preserves_minkowski C)
    simpa only [M, Matrix.transpose_mul, Matrix.mul_assoc] using h.trans hmetric
  have hdM : M.det = 1 := by
    simp [M, Matrix.det_mul, lorentzOfSL2C_det_one, hdet]
  obtain ⟨hblock, hR, hdR⟩ := rest_frame_block hM hdM hfix
  obtain ⟨B, hB⟩ := lift_rest_rotation _ hR hdR
  refine ⟨U⁻¹ * boostZ η * B, ?_⟩
  have hC : U⁻¹ * boostZ η = C⁻¹ := by
    dsimp only [C]
    rw [_root_.mul_inv_rev, boostZ_neg, inv_inv]
  rw [hC, lorentzOfSL2C_mul, hB, ← hblock]
  dsimp only [M]
  rw [← Matrix.mul_assoc, ← lorentzOfSL2C_mul,
    inv_mul_cancel, lorentzOfSL2C_one, Matrix.one_mul]

def spinor_to_future_null (ψ : Fin 2 → ℂ) : V4 :=
  minkowski_from_pauliHerm (Matrix.of fun i j => ψ i * conj (ψ j))

theorem pauliHerm_spinor_outer (ψ : Fin 2 → ℂ) :
    pauliHerm (spinor_to_future_null ψ) = Matrix.of fun i j => ψ i * conj (ψ j) := by
  apply minkowski_pauliHerm_inverse
  exact IsHermitian.ext fun i j => by
    simp [mul_comm]

theorem spinor_to_future_null_null (ψ : Fin 2 → ℂ) :
    minkowskiNormSq (spinor_to_future_null ψ) = 0 := by
  apply Complex.ofReal_injective
  rw [← pauliHerm_det, pauliHerm_spinor_outer, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Complex.ofReal_zero]
  ring

theorem spinor_to_future_null_time_nonneg (ψ : Fin 2 → ℂ) : 0 ≤ spinor_to_future_null ψ 0 := by
  simp [spinor_to_future_null, minkowski_from_pauliHerm, Complex.mul_re, ← sq]
  positivity

theorem spinor_to_future_null_equivariant (A : SL2C) (ψ : Fin 2 → ℂ) :
    lorentzOfSL2C A *ᵥ spinor_to_future_null ψ = spinor_to_future_null ((A : H2) *ᵥ ψ) := by
  apply pauliHerm_injective
  rw [lorentzOfSL2C_mulVec, pauliHerm_lorentzVec, pauliHerm_spinor_outer, pauliHerm_spinor_outer]
  ext i j
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Matrix.conjTranspose_apply]
  ring

def sl2c_celestial_mobius (A : SL2C) (z : ℂ) : ℂ :=
  ((A : H2) 0 0 * z + (A : H2) 0 1) / ((A : H2) 1 0 * z + (A : H2) 1 1)

theorem sl2c_celestial_mobius_equivariant (A : SL2C) (ψ : Fin 2 → ℂ)
    (h1 : ψ 1 ≠ 0) (hA1 : ((A : H2) *ᵥ ψ) 1 ≠ 0) :
    ((A : H2) *ᵥ ψ) 0 / ((A : H2) *ᵥ ψ) 1 = sl2c_celestial_mobius A (ψ 0 / ψ 1) := by
  let M : H2 := A
  have h (i : Fin 2) : (M *ᵥ ψ) i = (M i 0 * (ψ 0 / ψ 1) + M i 1) * ψ 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, add_mul, mul_assoc, h1]
  change (M *ᵥ ψ) 0 / (M *ᵥ ψ) 1 = _
  have hden : M 1 0 * (ψ 0 / ψ 1) + M 1 1 ≠ 0 := by
    intro hz
    exact hA1 (by rw [h 1, hz, zero_mul])
  rw [h 0, h 1]
  change (_ * ψ 1) / (_ * ψ 1) =
    (M 0 0 * (ψ 0 / ψ 1) + M 0 1) / (M 1 0 * (ψ 0 / ψ 1) + M 1 1)
  field_simp

end D5.S3.Geometry.Lorentz.SL2CLorentzCover4D
