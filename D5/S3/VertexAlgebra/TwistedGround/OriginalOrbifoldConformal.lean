/- GID: D5/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldConformal
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/OriginalOrbifoldConformal
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The original orbifold stress state gives the rank-24 Virasoro action. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldVertexAlgebra

/-! The conformal vector of the original orbifold and its two sector actions. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal

open LatticeGeneratingFieldLocality (LatticeData)
open HalfFockSpectralFiberSource (actualInverse actualInverse_left actualInverse_right)
open LatticeHalfFockChargedTensorCoefficients (ActualGround groundRank)
open LatticeHalfFock (tensorL tensorStressField stressCoeff)
open LatticeSugawaraCurrents (sugawaraMode)
open OriginalOrbifoldField (Carrier Y Y_fixed_ncoeff_apply)
open OriginalOrbifoldVertexAlgebra (originalVertexAlgebra)
open private stress stress_fixed_mode stress_twisted_mode from
  D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldTranslation
open private tensorEnd_tmul from D5.S3.VertexAlgebra.LatticeHalfFockTensorFields
open scoped VertexOperator TensorProduct

noncomputable section

/-- The inverse-Gram Sugawara vector embedded in the original fixed sector.
Its fixedness is the `theta_omega_fixed` proof in the sector stress state. -/
def conformalVector (D : LatticeData) (hu : IsUnit D.G.det) : Carrier D hu :=
  (stress D, 0)

variable (D : LatticeData) (hu : IsUnit D.G.det)
  (hD : Matrix.PosDef (D.G.map (Int.cast : ℤ → ℝ)))

/-- The coefficient of `z^(-m-2)` in the original field of the conformal vector. -/
def L (m : ℤ) : Module.End ℂ (Carrier D hu) :=
  (Y D hu hD (conformalVector D hu))[[m + 1]]

theorem L_eq_mode (h24 : D.rank = 24) (m : ℤ) :
    L D hu hD m =
      ((originalVertexAlgebra D hu hD h24).stateField (conformalVector D hu))[[m + 1]] := rfl

/-- On the fixed sector the coefficient is the actual inverse-Gram Sugawara mode. -/
theorem L_fixed_apply (m : ℤ) (a : Carrier D hu) :
    (L D hu hD m a).1.val = sugawaraMode D (actualInverse D) m a.1.val := by
  rw [L, conformalVector, Y_fixed_ncoeff_apply]
  exact LinearMap.congr_fun (LatticeActualConformalState.omega_modes D (actualInverse D) m)
    a.1.val

/-- On the negative parity sector the coefficient is the folded, corrected
half-Fock stress mode tensored with the identity on the actual ground space. -/
theorem L_twisted_apply (m : ℤ) (a : Carrier D hu) :
    (L D hu hD m a).2.val = tensorL D (ActualGround D hu) (actualInverse D) m a.2.val := by
  rw [L, conformalVector, Y_fixed_ncoeff_apply]
  change (LatticeHalfFockCorrectedField.correctedField D hu
      (LatticeActualConformalState.omega D (actualInverse D))).coeff
        (2 * (-(m + 1) - 1)) a.2.val = _
  rw [LatticeHalfFockCorrectedConformal.correctedField_omega D hu _ (actualInverse_left D hu)]
  simp only [tensorStressField, HVertexOperator.coeff_of_coeff, stressCoeff,
    show (2 * (-(m + 1) - 1)) % 2 = 0 by omega, ite_true,
    show (-(2 * (-(m + 1) - 1)) - 4) / 2 = m by omega, tensorL]

private theorem tensorL_virasoro (m n : ℤ) :
    let A := tensorL D (ActualGround D hu) (actualInverse D)
    A m * A n - A n * A m =
      ((m - n : ℤ) : ℂ) • A (m + n) +
        (if m + n = 0 then (D.rank : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • 1 := by
  dsimp only
  apply TensorProduct.ext'
  intro p g
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply, tensorL, tensorEnd_tmul,
    ← TensorProduct.sub_tmul]
  have h := LinearMap.congr_fun
    (LatticeHalfFock.L_virasoro D (actualInverse D) (actualInverse_left D hu)
      (actualInverse_right D hu) m n) p
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply] at h
  rw [Int.cast_sub, h, TensorProduct.add_tmul]
  simp only [← TensorProduct.smul_tmul']

/-- The commutator on the assembled state space has central charge 24. -/
theorem L_virasoro (h24 : D.rank = 24) (m n : ℤ) :
    L D hu hD m * L D hu hD n - L D hu hD n * L D hu hD m =
      ((m - n : ℤ) : ℂ) • L D hu hD (m + n) +
        (if m + n = 0 then (24 : ℂ) / 12 * ((m : ℂ)^3 - m) else 0) • 1 := by
  apply LinearMap.ext
  intro a
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply,
    LinearMap.smul_apply, Module.End.one_apply]
  apply Prod.ext <;> apply Subtype.ext
  · simpa only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Submodule.coe_sub,
      Submodule.coe_add, Submodule.coe_smul, L_fixed_apply, h24, Nat.cast_ofNat,
      LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using LinearMap.congr_fun
        (LatticeSugawaraVirasoro.sugawaraMode_virasoro D (actualInverse D)
          (actualInverse_left D hu) (actualInverse_right D hu) m n) a.1.val
  · simpa only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Submodule.coe_sub,
      Submodule.coe_add, Submodule.coe_smul, L_twisted_apply, h24, Nat.cast_ofNat,
      LinearMap.sub_apply, Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply,
      Module.End.one_apply] using LinearMap.congr_fun (tensorL_virasoro D hu m n) a.2.val

/-- The minus-one Virasoro mode is the translation of the original vertex algebra. -/
theorem L_minus_one_eq_translation (h24 : D.rank = 24) :
    L D hu hD (-1) = (originalVertexAlgebra D hu hD h24).translation := by
  apply LinearMap.ext
  intro a
  rw [L, conformalVector, Y_fixed_ncoeff_apply, show (-1 : ℤ) + 1 = 0 by decide,
    stress_fixed_mode D hu, stress_twisted_mode D hu]
  rfl

open LatticePositiveEnergy (Label carrierCoeffEquiv energy)
open LatticeHalfFockGradedTrace (OddMonomial actualAmbientBasis actualTensorL0 actualTensorL0_repr
  oddWeight)
open LatticeTwistedGroundRealization (Half)

/-- The zero mode on each fixed-sector charge/monomial coefficient is its lattice energy. -/
theorem L_zero_fixed_coeff (a : Carrier D hu) (i : Label D) :
    carrierCoeffEquiv D (L D hu hD 0 a).1.val i =
      (energy D i : ℂ) * carrierCoeffEquiv D a.1.val i := by
  rw [L_fixed_apply]
  exact LatticePositiveEnergy.actualL0_coeff D (actualInverse D)
    (actualInverse_left D hu) (actualInverse_right D hu) a.1.val i

/-- The zero mode on the negative parity sector is the actual tensor energy operator. -/
theorem L_zero_twisted (a : Carrier D hu) :
    (L D hu hD 0 a).2.val = actualTensorL0 D hu a.2.val :=
  L_twisted_apply D hu hD 0 a

/-- The negative sector retains the half-Fock degree and the exact vacuum shift. -/
theorem L_zero_twisted_coeff (a : Carrier D hu) (i : OddMonomial D × Half (groundRank D hu)) :
    (actualAmbientBasis D hu).repr (L D hu hD 0 a).2.val i =
      ((oddWeight D i.1 : ℂ) / 2 + (D.rank : ℂ) / 16) *
        (actualAmbientBasis D hu).repr a.2.val i := by
  rw [L_zero_twisted]
  simpa only [add_comm] using actualTensorL0_repr D hu a.2.val i

#print axioms conformalVector
#print axioms L
#print axioms L_eq_mode
#print axioms L_fixed_apply
#print axioms L_twisted_apply
#print axioms L_virasoro
#print axioms L_minus_one_eq_translation
#print axioms L_zero_fixed_coeff
#print axioms L_zero_twisted
#print axioms L_zero_twisted_coeff

end
end D5.S3.VertexAlgebra.TwistedGround.OriginalOrbifoldConformal
