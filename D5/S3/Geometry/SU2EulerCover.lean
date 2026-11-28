/- GID: D5/S3/Geometry/SU2EulerCover
   generality: G
   mirror-B: none(waiver:covered-by-sl2-clorentz-cover4-d-blueprint)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Euler factorizations in two complex and three real dimensions. -/

import OmegaBuild.Commands
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Omega original.
Euler factorizations in two complex and three real dimensions. The complex argument
chooses phases also when a coordinate vanishes. -/

compile_only_with_mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OmegaMath.SU2EulerCover

open Matrix
open scoped ComplexConjugate

abbrev H2 := Matrix (Fin 2) (Fin 2) ℂ
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

private def phase (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

private theorem phase_add (θ φ : ℝ) : phase (θ + φ) = phase θ * phase φ := by
  simp [phase, add_mul, Complex.exp_add]

private theorem phase_neg (θ : ℝ) : phase (-θ) = conj (phase θ) := by
  simp [phase, ← Complex.exp_conj, mul_neg, neg_mul]

/-- The half-angle spinor lift of a rotation about the third spatial axis. -/
def rotZ (θ : ℝ) : SL2C :=
  ⟨!![phase (-θ / 2), 0; 0, phase (θ / 2)], by
    rw [det_fin_two_of, zero_mul, sub_zero, ← phase_add]
    simp [phase, show -θ / 2 + θ / 2 = 0 by ring]⟩

theorem coe_rotZ (θ : ℝ) :
    (rotZ θ : H2) =
      !![Complex.exp ((↑(-θ / 2) : ℂ) * Complex.I), 0;
        0, Complex.exp ((↑(θ / 2) : ℂ) * Complex.I)] := rfl

/-- The half-angle spinor lift of a rotation about the second spatial axis. -/
def rotY (φ : ℝ) : SL2C :=
  ⟨!![(Real.cos (φ / 2) : ℂ), -(Real.sin (φ / 2) : ℂ);
      (Real.sin (φ / 2) : ℂ), (Real.cos (φ / 2) : ℂ)], by
    rw [det_fin_two_of, neg_mul, sub_neg_eq_add]
    exact_mod_cast (show Real.cos (φ / 2) * Real.cos (φ / 2) +
        Real.sin (φ / 2) * Real.sin (φ / 2) = 1 by
      rw [← sq, ← sq, add_comm, Real.sin_sq_add_cos_sq])⟩

theorem coe_rotY (φ : ℝ) :
    (rotY φ : H2) =
      !![(Real.cos (φ / 2) : ℂ), -(Real.sin (φ / 2) : ℂ);
        (Real.sin (φ / 2) : ℂ), (Real.cos (φ / 2) : ℂ)] := rfl

/-- The diagonal spinor lift for rapidity along the third spatial axis. -/
def boostZ (η : ℝ) : SL2C :=
  ⟨!![(Real.exp (η / 2) : ℂ), 0; 0, (Real.exp (-η / 2) : ℂ)], by
    rw [det_fin_two_of, zero_mul, sub_zero, ← Complex.ofReal_mul, ← Real.exp_add]
    simp [show η / 2 + -η / 2 = 0 by ring]⟩

theorem coe_boostZ (η : ℝ) :
    (boostZ η : H2) = !![(Real.exp (η / 2) : ℂ), 0; 0, (Real.exp (-η / 2) : ℂ)] := rfl

theorem boostZ_neg (η : ℝ) : boostZ (-η) = (boostZ η)⁻¹ := by
  apply Subtype.coe_injective
  change (boostZ (-η) : H2) = (↑((boostZ η)⁻¹) : H2)
  rw [SpecialLinearGroup.coe_inv, coe_boostZ, coe_boostZ, adjugate_fin_two_of]
  simp

theorem rotZ_unitary (θ : ℝ) : (rotZ θ : H2)ᴴ * (rotZ θ : H2) = 1 := by
  have hneg : conj (phase (θ / 2)) = phase (-θ / 2) := by rw [← phase_neg, neg_div]
  have hpos : conj (phase (-θ / 2)) = phase (θ / 2) := by
    rw [← phase_neg, neg_div, neg_neg]
  have hprod : phase (θ / 2) * phase (-θ / 2) = 1 := by
    rw [← phase_add, show θ / 2 + -θ / 2 = 0 by ring]
    simp [phase]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ, Matrix.mul_apply, Fin.sum_univ_two, hneg, hpos, hprod,
      mul_comm (phase (-θ / 2))]

theorem rotY_unitary (φ : ℝ) : (rotY φ : H2)ᴴ * (rotY φ : H2) = 1 := by
  have hnorm : (Real.cos (φ / 2) : ℂ) ^ 2 + (Real.sin (φ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast (add_comm _ _).trans (Real.sin_sq_add_cos_sq (φ / 2))
  rw [coe_rotY]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    first | linear_combination hnorm | ring

private theorem unitary_sl2_entries (U : SL2C) (hU : (U : H2)ᴴ * (U : H2) = 1) :
    (U : H2) 0 1 = -conj ((U : H2) 1 0) ∧
    (U : H2) 1 1 = conj ((U : H2) 0 0) := by
  have huInv : (U : H2)ᴴ = (↑(U⁻¹) : H2) := by
    calc
      (U : H2)ᴴ = (U : H2)ᴴ * ((U : H2) * (↑(U⁻¹) : H2)) := by
        rw [← SpecialLinearGroup.coe_mul, mul_inv_cancel, SpecialLinearGroup.coe_one, mul_one]
      _ = (↑(U⁻¹) : H2) := by rw [← Matrix.mul_assoc, hU, one_mul]
  rw [SpecialLinearGroup.coe_inv, adjugate_fin_two] at huInv
  constructor
  · have h : conj ((U : H2) 1 0) = -(U : H2) 0 1 := by
      simpa using congrArg (fun M : H2 => M 0 1) huInv
    simpa using (congrArg Neg.neg h).symm
  · simpa [eq_comm] using congrArg (fun M : H2 => M 0 0) huInv

/-- Every determinant-one unitary matrix is a product of three half-angle rotations. -/
theorem su2_euler (U : SL2C) (hU : (U : H2)ᴴ * (U : H2) = 1) :
    ∃ α β γ : ℝ, U = rotZ α * rotY β * rotZ γ := by
  let a := (U : H2) 0 0
  let b := (U : H2) 1 0
  obtain ⟨hab, haa⟩ := unitary_sl2_entries U hU
  have hunit : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1 := by
    have he := congrArg (fun M : H2 => M 0 0) hU
    have hComplex : (‖a‖ : ℂ) ^ 2 + (‖b‖ : ℂ) ^ 2 = 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, a, b, Complex.conj_mul'] using he
    exact_mod_cast hComplex
  let m : ℂ := ⟨‖a‖, ‖b‖⟩
  have hm : ‖m‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [m, pow_two] using hunit
  let α := b.arg - a.arg
  let β := 2 * m.arg
  let γ := -a.arg - b.arg
  have hc : Real.cos (β / 2) = ‖a‖ := by
    simpa [β, hm, m, show 2 * m.arg / 2 = m.arg by ring] using Complex.norm_mul_cos_arg m
  have hs : Real.sin (β / 2) = ‖b‖ := by
    simpa [β, hm, m, show 2 * m.arg / 2 = m.arg by ring] using Complex.norm_mul_sin_arg m
  have ha : (‖a‖ : ℂ) * phase a.arg = a := Complex.norm_mul_exp_arg_mul_I a
  have hb : (‖b‖ : ℂ) * phase b.arg = b := Complex.norm_mul_exp_arg_mul_I b
  have hca : (‖a‖ : ℂ) * phase (-a.arg) = conj a := by
    simpa [phase_neg, map_mul] using congrArg (conj : ℂ → ℂ) ha
  have hcb : (‖b‖ : ℂ) * phase (-b.arg) = conj b := by
    simpa [phase_neg, map_mul] using congrArg (conj : ℂ → ℂ) hb
  refine ⟨α, β, γ, Subtype.coe_injective ?_⟩
  change (U : H2) = (↑(rotZ α * rotY β * rotZ γ) : H2)
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, coe_rotY, hc, hs]
  change (U : H2) =
    !![phase (-α / 2), 0; 0, phase (α / 2)] *
      !![(‖a‖ : ℂ), -(‖b‖ : ℂ); (‖b‖ : ℂ), (‖a‖ : ℂ)] *
      !![phase (-γ / 2), 0; 0, phase (γ / 2)]
  have h00 : -α / 2 + -γ / 2 = a.arg := by dsimp [α, γ]; ring
  have h01 : -α / 2 + γ / 2 = -b.arg := by dsimp [α, γ]; ring
  have h10 : α / 2 + -γ / 2 = b.arg := by dsimp [α, γ]; ring
  have h11 : α / 2 + γ / 2 = -a.arg := by dsimp [α, γ]; ring
  have combine (z : ℂ) (s t : ℝ) : phase s * z * phase t = z * phase (s + t) := by
    rw [phase_add]
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, combine, h00, h01, h10, h11, hab, haa,
      ha, hb, hca, hcb] <;> rfl

abbrev R3 := Matrix (Fin 3) (Fin 3) ℝ

/-- Active right-handed rotation about the third axis. -/
def rotZ3 (θ : ℝ) : R3 :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- Active right-handed rotation about the second axis. -/
def rotY3 (φ : ℝ) : R3 :=
  !![Real.cos φ, 0, Real.sin φ; 0, 1, 0; -Real.sin φ, 0, Real.cos φ]

private theorem rotZ3_transpose (θ : ℝ) : (rotZ3 θ)ᵀ = rotZ3 (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotZ3, Real.cos_neg, Real.sin_neg]

private theorem rotY3_transpose (θ : ℝ) : (rotY3 θ)ᵀ = rotY3 (-θ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [rotY3, Real.cos_neg, Real.sin_neg]

private theorem rotZ3_orthogonal (θ : ℝ) : (rotZ3 θ)ᵀ * rotZ3 θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ3, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination Real.sin_sq_add_cos_sq θ | ring

private theorem rotY3_orthogonal (θ : ℝ) : (rotY3 θ)ᵀ * rotY3 θ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotY3, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | linear_combination Real.sin_sq_add_cos_sq θ | ring

theorem rotZ3_det (θ : ℝ) : (rotZ3 θ).det = 1 := by
  simp [rotZ3, det_fin_three]
  linear_combination Real.sin_sq_add_cos_sq θ

theorem rotY3_det (θ : ℝ) : (rotY3 θ).det = 1 := by
  simp [rotY3, det_fin_three]
  linear_combination Real.sin_sq_add_cos_sq θ

/-- Two axial rotations send any vector to the nonnegative third axis. -/
theorem align_spatial (w : Fin 3 → ℝ) :
    ∃ α β : ℝ, (rotY3 β * rotZ3 α) *ᵥ w =
      ![0, 0, Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2)] := by
  let p : ℂ := ⟨w 0, w 1⟩
  let q : ℂ := ⟨w 2, ‖p‖⟩
  have hp₀ : ‖p‖ * Real.cos p.arg = w 0 := Complex.norm_mul_cos_arg p
  have hp₁ : ‖p‖ * Real.sin p.arg = w 1 := Complex.norm_mul_sin_arg p
  have hq₀ : ‖q‖ * Real.cos q.arg = w 2 := Complex.norm_mul_cos_arg q
  have hq₁ : ‖q‖ * Real.sin q.arg = ‖p‖ := Complex.norm_mul_sin_arg q
  have hq : ‖q‖ = Real.sqrt (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) := by
    rw [Complex.norm_def, Complex.normSq_apply]
    change √(w 2 * w 2 + ‖p‖ * ‖p‖) = _
    rw [Complex.norm_mul_self_eq_normSq, Complex.normSq_apply]
    change √(w 2 * w 2 + (w 0 * w 0 + w 1 * w 1)) = _
    congr 1
    ring
  have hZ : rotZ3 (-p.arg) *ᵥ w = ![‖p‖, 0, w 2] := by
    funext i
    fin_cases i <;> simp [rotZ3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_neg, Real.sin_neg]
    · rw [← hp₀, ← hp₁]
      linear_combination ‖p‖ * Real.sin_sq_add_cos_sq p.arg
    · rw [← hp₀, ← hp₁]
      ring
  have hY : rotY3 (-q.arg) *ᵥ ![‖p‖, 0, w 2] = ![0, 0, ‖q‖] := by
    funext i
    fin_cases i <;> simp [rotY3, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.cos_neg, Real.sin_neg]
    · rw [← hq₀, ← hq₁]
      ring
    · rw [← hq₀, ← hq₁]
      linear_combination ‖q‖ * Real.sin_sq_add_cos_sq q.arg
  exact ⟨-p.arg, -q.arg, by rw [← mulVec_mulVec, hZ, hY, hq]⟩

private theorem rotation_fixing_third_axis (R : R3) (hR : Rᵀ * R = 1)
    (hdet : R.det = 1) (hfix : R *ᵥ Pi.single (2 : Fin 3) 1 = Pi.single (2 : Fin 3) (1 : ℝ)) :
    ∃ γ : ℝ, R = rotZ3 γ := by
  have hTranspose : Rᵀ *ᵥ Pi.single (2 : Fin 3) 1 = Pi.single (2 : Fin 3) (1 : ℝ) := by
    conv_lhs => rw [← hfix, mulVec_mulVec, hR, one_mulVec]
  have hcol (i : Fin 3) : R i 2 = (Pi.single (2 : Fin 3) 1 : Fin 3 → ℝ) i := by
    simpa only [mulVec_single_one, Matrix.col_apply] using congrArg (fun v : Fin 3 → ℝ => v i) hfix
  have hrow (i : Fin 3) : R 2 i = (Pi.single (2 : Fin 3) 1 : Fin 3 → ℝ) i := by
    simpa only [mulVec_single_one, Matrix.col_apply, transpose_apply] using
      congrArg (fun v : Fin 3 → ℝ => v i) hTranspose
  have h02 : R 0 2 = 0 := by simpa using hcol 0
  have h12 : R 1 2 = 0 := by simpa using hcol 1
  have h20 : R 2 0 = 0 := by simpa using hrow 0
  have h21 : R 2 1 = 0 := by simpa using hrow 1
  have h22 : R 2 2 = 1 := by simpa using hcol 2
  have ha : R 0 0 * R 0 0 + R 1 0 * R 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h20] using congrArg (fun M : R3 => M 0 0) hR
  have horth : R 0 0 * R 0 1 + R 1 0 * R 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, h20] using congrArg (fun M : R3 => M 0 1) hR
  have hminor : R 0 0 * R 1 1 - R 0 1 * R 1 0 = 1 := by
    simpa [det_fin_three, h02, h12, h20, h21, h22] using hdet
  have h11 : R 1 1 = R 0 0 := by
    linear_combination R 0 0 * hminor + R 1 0 * horth - R 1 1 * ha
  have h01 : R 0 1 = -R 1 0 := by
    linear_combination R 0 0 * horth - R 0 1 * ha - R 1 0 * hminor
  let z : ℂ := ⟨R 0 0, R 1 0⟩
  have hz : ‖z‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simpa [z] using ha
  have hcos : Real.cos z.arg = R 0 0 := by
    simpa [hz, z] using Complex.norm_mul_cos_arg z
  have hsin : Real.sin z.arg = R 1 0 := by
    simpa [hz, z] using Complex.norm_mul_sin_arg z
  refine ⟨z.arg, ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZ3, hcos, hsin, h01, h11, h02, h12, h20, h21, h22]

/-- Every real special orthogonal matrix of order three has a ZYZ Euler factorization. -/
theorem so3_euler (R : R3) (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    ∃ α β γ : ℝ, R = rotZ3 α * rotY3 β * rotZ3 γ := by
  let w : Fin 3 → ℝ := fun i => R i 2
  have hw : w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2 = 1 := by
    simpa [w, Matrix.mul_apply, Fin.sum_univ_three, pow_two]
      using congrArg (fun M : R3 => M 2 2) hR
  obtain ⟨α, β, hAlign⟩ := align_spatial w
  let S := (rotY3 β * rotZ3 α) * R
  have hS : Sᵀ * S = 1 := by
    unfold S
    rw [transpose_mul, transpose_mul]
    calc
      (Rᵀ * ((rotZ3 α)ᵀ * (rotY3 β)ᵀ)) * ((rotY3 β * rotZ3 α) * R) =
          Rᵀ * ((rotZ3 α)ᵀ * (((rotY3 β)ᵀ * rotY3 β) * (rotZ3 α * R))) := by
            simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [rotY3_orthogonal, one_mul, ← Matrix.mul_assoc (rotZ3 α)ᵀ,
          rotZ3_orthogonal, one_mul, hR]
  have hSdet : S.det = 1 := by
    simp [S, det_mul, rotZ3_det, rotY3_det, hdet]
  have hSfix : S *ᵥ Pi.single (2 : Fin 3) 1 = Pi.single (2 : Fin 3) (1 : ℝ) := by
    have hcol : R *ᵥ Pi.single (2 : Fin 3) 1 = w := by
      funext i
      simp [w]
    rw [show S = (rotY3 β * rotZ3 α) * R from rfl, ← mulVec_mulVec, hcol, hAlign, hw,
      Real.sqrt_one]
    funext i
    fin_cases i <;> simp
  obtain ⟨γ, hγ⟩ := rotation_fixing_third_axis S hS hSdet hSfix
  refine ⟨-α, -β, γ, ?_⟩
  rw [← rotZ3_transpose, ← rotY3_transpose, ← hγ]
  unfold S
  calc
    R = (rotZ3 α)ᵀ * (rotZ3 α * R) := by rw [← Matrix.mul_assoc, rotZ3_orthogonal, one_mul]
    _ = (rotZ3 α)ᵀ * (rotY3 β)ᵀ * ((rotY3 β * rotZ3 α) * R) := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc (rotY3 β), ← Matrix.mul_assoc (rotY3 β)ᵀ,
        rotY3_orthogonal, one_mul]

end OmegaMath.SU2EulerCover
