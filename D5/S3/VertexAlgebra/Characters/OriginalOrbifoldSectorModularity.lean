/- GID: D5/S3/VertexAlgebra/Characters/OriginalOrbifoldSectorModularity
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/Characters/OriginalOrbifoldSectorModularity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Modular S and T permute the signed and twisted rank-24 Leech orbifold sectors. -/

import D5.S3.VertexAlgebra.Characters.LatticeThetaCharacter
import D5.S3.VertexAlgebra.Lattice.ActualLeechHyperbolic
import Mathlib.NumberTheory.ModularForms.Discriminant

/-! The signed trace and the two twisted traces of the Leech orbifold on the upper half-plane. -/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm
open Complex

namespace D5.S3.VertexAlgebra.OriginalOrbifoldSectorModularity

open ActualLeechHyperbolic (leechData leech_spec)
open LatticePositiveEnergy (complex_inverse_exists)
open LatticeThetaCharacter (actualThetaCharacter actual_theta_character_eta
  actual_theta_character_S)

local notation "Δ" => ModularForm.discriminant
local notation "S" => ModularGroup.S
local notation "T" => ModularGroup.T

/-- Doubling the upper-half-plane coordinate. -/
def double (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨2 * (τ : ℂ), by simpa [Complex.mul_im] using mul_pos two_pos τ.im_pos⟩

/-- Halving the upper-half-plane coordinate. -/
def half (τ : UpperHalfPlane) : UpperHalfPlane :=
  ⟨(τ : ℂ) / 2, by simpa using half_pos τ.im_pos⟩

@[simp] theorem coe_double (τ : UpperHalfPlane) : (double τ : ℂ) = 2 * (τ : ℂ) := rfl

@[simp] theorem coe_half (τ : UpperHalfPlane) : (half τ : ℂ) = (τ : ℂ) / 2 := rfl

private theorem coe_T (τ : UpperHalfPlane) : (↑(T • τ) : ℂ) = τ + 1 := by
  rw [UpperHalfPlane.modular_T_smul]
  simp [add_comm]

private theorem coe_S (τ : UpperHalfPlane) : (↑(S • τ) : ℂ) = -1 / τ := by
  rw [UpperHalfPlane.modular_S_smul]
  simp [neg_div, one_div]

/-- The signed untwisted sector, with the central charge shift. -/
def B (τ : UpperHalfPlane) : ℂ := Δ τ / Δ (double τ)

/-- The twisted sector with the identity insertion and its rank-24 ground multiplicity. -/
def C (τ : UpperHalfPlane) : ℂ := (2 : ℂ) ^ (12 : ℕ) * Δ τ / Δ (half τ)

/-- The translate of the twisted identity trace. -/
def D (τ : UpperHalfPlane) : ℂ := C (T • τ)

/-- Eta form of the signed sector. -/
theorem B_eq_eta (τ : UpperHalfPlane) :
    B τ = (ModularForm.eta τ / ModularForm.eta (2 * (τ : ℂ))) ^ (24 : ℕ) := by
  simp only [B, ModularForm.discriminant, coe_double, div_pow]

/-- Eta form of the twisted identity sector. -/
theorem C_eq_eta (τ : UpperHalfPlane) :
    C τ = (2 : ℂ) ^ (12 : ℕ) *
      (ModularForm.eta τ / ModularForm.eta ((τ : ℂ) / 2)) ^ (24 : ℕ) := by
  simp only [C, ModularForm.discriminant, coe_half, div_pow, mul_div_assoc]

/-- Eta form of the translated twisted sector, with both arguments translated. -/
theorem D_eq_eta (τ : UpperHalfPlane) :
    D τ = (2 : ℂ) ^ (12 : ℕ) *
      (ModularForm.eta ((τ : ℂ) + 1) / ModularForm.eta (((τ : ℂ) + 1) / 2)) ^ (24 : ℕ) := by
  rw [D, C_eq_eta, coe_T]

private theorem discriminant_T (τ : UpperHalfPlane) : Δ (T • τ) = Δ τ := by
  have h := (ModularForm.slash_action_eq'_iff 12 Δ T τ).mp
    (congrFun ModularForm.discriminant_T_invariant τ)
  simpa [ModularGroup.T] using h

private theorem discriminant_S (τ : UpperHalfPlane) :
    Δ (S • τ) = (τ : ℂ) ^ (12 : ℕ) * Δ τ := by
  have h := (ModularForm.slash_action_eq'_iff 12 Δ S τ).mp
    (congrFun ModularForm.discriminant_S_invariant τ)
  simpa [ModularGroup.S] using h

/-- In `D(τ)` the numerator can be evaluated at `τ` while the denominator is
evaluated at `(τ + 1) / 2`. -/
theorem D_eq (τ : UpperHalfPlane) :
    D τ = (2 : ℂ) ^ (12 : ℕ) * Δ τ / Δ (half (T • τ)) := by
  rw [D, C, discriminant_T]

/-- Inversion takes the signed untwisted trace to the twisted identity trace. -/
theorem B_S (τ : UpperHalfPlane) : B (S • τ) = C τ := by
  obtain ⟨H, hHG, hGH⟩ := complex_inverse_exists leechData leech_spec.2.2.1
  have hB := (actual_theta_character_eta leechData H hHG hGH
    (S • τ : UpperHalfPlane) (S • τ : UpperHalfPlane).im_pos).2.2
  have hC := (actual_theta_character_S leechData H hHG hGH τ τ.im_pos).1
  rw [leech_spec.1, ← B_eq_eta] at hB
  rw [leech_spec.1, show ((↑(24 : ℕ) : ℂ) / 2) = (↑(12 : ℕ) : ℂ) by norm_num,
    Complex.cpow_natCast, ← C_eq_eta] at hC
  rw [coe_S] at hB
  exact hB.symm.trans hC

/-- Inversion takes the twisted identity trace to the signed untwisted trace. -/
theorem C_S (τ : UpperHalfPlane) : C (S • τ) = B τ := by
  have hSS : S • (S • τ) = τ := by
    apply UpperHalfPlane.ext
    rw [coe_S, coe_S]
    field_simp [τ.ne_zero]
  rw [← B_S (S • τ), hSS]

private def twistedMatrix : SL(2, ℤ) :=
  ⟨!![1, -1; 2, -1], by norm_num [Matrix.det_fin_two_of]⟩

private theorem twistedMatrix_denom (τ : UpperHalfPlane) :
    (twistedMatrix 1 0 : ℂ) * (half (T • τ) : ℂ) + (twistedMatrix 1 1 : ℂ) = τ := by
  have h : (2 : ℂ) * (half (T • τ) : ℂ) - 1 = τ := by
    rw [coe_half, coe_T]
    ring
  simpa [twistedMatrix, sub_eq_add_neg] using h

private theorem twistedMatrix_smul (τ : UpperHalfPlane) :
    twistedMatrix • half (T • τ) = half (T • (S • τ)) := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_half (T • (S • τ)),
    coe_T (S • τ), coe_S]
  simp only [algebraMap_int_eq, Int.coe_castRingHom, Complex.ofReal_intCast]
  rw [twistedMatrix_denom, coe_half, coe_T]
  norm_num [twistedMatrix]
  field_simp [τ.ne_zero] <;> ring

/-- Inversion fixes the translated twisted trace. The denominator transforms
at `z = (τ + 1) / 2` by the weight-12 action of `[[1,-1],[2,-1]]`. -/
theorem D_S (τ : UpperHalfPlane) : D (S • τ) = D τ := by
  have hInvariant : (Δ ∣[(12 : ℤ)] twistedMatrix) = Δ := by
    rw [ModularForm.SL_slash]
    simpa only [CuspForm.coe_discriminant] using
      SlashInvariantForm.slash_action_eqn CuspForm.discriminant
        (twistedMatrix : GL (Fin 2) ℝ) (show (twistedMatrix : GL (Fin 2) ℝ) ∈ 𝒮ℒ from
          ⟨twistedMatrix, rfl⟩)
  have hΔ := (ModularForm.slash_action_eq'_iff 12 Δ twistedMatrix (half (T • τ))).mp
    (congrFun hInvariant (half (T • τ)))
  rw [twistedMatrix_smul, twistedMatrix_denom, zpow_ofNat] at hΔ
  rw [D_eq, D_eq, discriminant_S, hΔ, mul_left_comm ((2 : ℂ) ^ (12 : ℕ)),
    mul_div_mul_left _ _ (pow_ne_zero _ τ.ne_zero)]

/-- Translation fixes the signed untwisted trace. -/
theorem B_T (τ : UpperHalfPlane) : B (T • τ) = B τ := by
  have h : double (T • τ) = T • (T • double τ) := by
    apply UpperHalfPlane.ext
    rw [coe_double, coe_T, coe_T, coe_T, coe_double]
    ring
  rw [B, B, h, discriminant_T, discriminant_T, discriminant_T]

/-- Translation takes the twisted identity trace to its translate. -/
theorem C_T (τ : UpperHalfPlane) : C (T • τ) = D τ := rfl

/-- Translation takes the translated twisted trace back to the identity trace. -/
theorem D_T (τ : UpperHalfPlane) : D (T • τ) = C τ := by
  have h : half (T • (T • τ)) = T • half τ := by
    apply UpperHalfPlane.ext
    rw [coe_half, coe_T, coe_T, coe_T, coe_half]
    ring
  rw [D_eq, C, h, discriminant_T, discriminant_T]

/-- The three sector contributions have a pointwise invariant sum under both generators. -/
theorem sector_sum_invariant (τ : UpperHalfPlane) :
    (B (S • τ) + C (S • τ) + D (S • τ) = B τ + C τ + D τ) ∧
    (B (T • τ) + C (T • τ) + D (T • τ) = B τ + C τ + D τ) := by
  constructor
  · rw [B_S, C_S, D_S, add_comm (C τ) (B τ)]
  · rw [B_T, C_T, D_T]
    ring

#print axioms double
#print axioms half
#print axioms coe_double
#print axioms coe_half
#print axioms B
#print axioms C
#print axioms D
#print axioms B_eq_eta
#print axioms C_eq_eta
#print axioms D_eq_eta
#print axioms D_eq
#print axioms B_S
#print axioms C_S
#print axioms D_S
#print axioms B_T
#print axioms C_T
#print axioms D_T
#print axioms sector_sum_invariant

end D5.S3.VertexAlgebra.OriginalOrbifoldSectorModularity
