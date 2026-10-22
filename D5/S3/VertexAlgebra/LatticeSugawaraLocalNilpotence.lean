/- GID: D5/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/LatticeSugawaraLocalNilpotence
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Sugawara one-mode powers vanish beyond native finite oscillator support. -/

import D5.S3.VertexAlgebra.LatticeActualLZeroGrading
import D5.S3.VertexAlgebra.LatticeHalfFockTargetThetaCorrectionWeight

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence

open LatticeGeneratingFieldLocality LatticePositiveEnergy
open LatticeSugawaraCurrents LatticeSugawaraVirasoro LatticeSugawaraConformal
open scoped BigOperators

noncomputable section

def oscillatorBound (D : LatticeData) (v : Carrier D) : ℕ :=
  (carrierCoeffEquiv D v).support.sup (fun a => oscillatorEnergy a.2)

private theorem euler_basis (D : LatticeData) (a : Label D) :
    eulerMode D (carrierBasis D a) =
      (oscillatorEnergy a.2 : ℂ) • carrierBasis D a := by
  rw [carrierBasis_apply]
  simp only [eulerMode, Finsupp.lsum_single, LinearMap.comp_apply, Finsupp.lsingle_apply, Derivation.coeFn_coe]
  rw [LatticeHalfFockCorrectionGrading.oscillatorEuler_monomial]
  simp only [oscillatorEnergy, Finsupp.smul_single]

private theorem euler_coeff (D : LatticeData) (v : Carrier D) (a : Label D) :
    carrierCoeffEquiv D (eulerMode D v) a =
      (oscillatorEnergy a.2 : ℂ) * carrierCoeffEquiv D v a := by
  classical
  let coefficient : Carrier D →ₗ[ℂ] ℂ :=
    (Finsupp.lapply a).comp (carrierCoeffEquiv D).toLinearMap
  have diagonal : coefficient.comp (eulerMode D) =
      (oscillatorEnergy a.2 : ℂ) • coefficient := by
    apply (carrierBasis D).ext
    intro label
    change coefficient (eulerMode D (carrierBasis D label)) =
      (oscillatorEnergy a.2 : ℂ) • coefficient (carrierBasis D label)
    rw [euler_basis, map_smul]
    change (oscillatorEnergy label.2 : ℂ) *
        carrierCoeffEquiv D (carrierBasis D label) a =
      (oscillatorEnergy a.2 : ℂ) * carrierCoeffEquiv D (carrierBasis D label) a
    rw [carrierCoeffEquiv_basis]
    by_cases same : label = a
    · subst label
      rfl
    · simp only [Finsupp.single_apply, if_neg same, mul_zero, smul_eq_mul]
  exact LinearMap.congr_fun diagonal v

private theorem euler_one_eigen (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ)
    (v : Carrier D) (weight : ℂ) (eigen : eulerMode D v = weight • v) :
    eulerMode D (sugawaraMode D H 1 v) =
      (weight - 1) • sugawaraMode D H 1 v := by
  have commutator := congrArg (fun operator : Module.End ℂ (Carrier D) => operator v)
    (eulerMode_sugawara_commutator D H 1)
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply,
    Int.cast_one, eigen, map_smul] at commutator
  rw [sub_eq_iff_eq_add] at commutator
  rw [commutator, sub_smul, one_smul]
  module

theorem one_pow_basis_euler (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Label D) (power : ℕ) :
    eulerMode D (((sugawaraMode D H 1)^power) (carrierBasis D a)) =
      ((oscillatorEnergy a.2 : ℂ) - (power : ℂ)) •
        (((sugawaraMode D H 1)^power) (carrierBasis D a)) := by
  induction power with
  | zero => simpa using euler_basis D a
  | succ power inductionHypothesis =>
    rw [pow_succ', Module.End.mul_apply]
    have next := euler_one_eigen D H _ _ inductionHypothesis
    convert next using 1 <;> push_cast <;> ring

theorem one_pow_basis_eq_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (a : Label D) (power : ℕ)
    (beyond : oscillatorEnergy a.2 < power) :
    ((sugawaraMode D H 1)^power) (carrierBasis D a) = 0 := by
  classical
  apply (carrierCoeffEquiv D).injective
  ext label
  have coefficient := congrArg (fun state : Carrier D => carrierCoeffEquiv D state label)
    (one_pow_basis_euler D H a power)
  rw [euler_coeff] at coefficient
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at coefficient
  have different : (oscillatorEnergy label.2 : ℂ) ≠
      (oscillatorEnergy a.2 : ℂ) - (power : ℂ) := by
    intro equal
    have integerEqual : (oscillatorEnergy label.2 : ℤ) =
        (oscillatorEnergy a.2 : ℤ) - (power : ℤ) := by
      exact_mod_cast equal
    omega
  simpa using (mul_eq_mul_right_iff.mp coefficient).resolve_left different

theorem one_pow_eq_zero (D : LatticeData)
    (H : Matrix (Fin D.rank) (Fin D.rank) ℂ) (v : Carrier D) (power : ℕ)
    (beyond : oscillatorBound D v < power) :
    ((sugawaraMode D H 1)^power) v = 0 := by
  classical
  conv_lhs =>
    rw [← (carrierBasis D).linearCombination_repr v,
      Finsupp.linearCombination_apply, Finsupp.sum]
  simp only [map_sum, map_smul]
  apply Finset.sum_eq_zero
  intro label present
  have below : oscillatorEnergy label.2 ≤ oscillatorBound D v :=
    Finset.le_sup (f := fun a : Label D => oscillatorEnergy a.2) present
  rw [one_pow_basis_eq_zero D H label power (lt_of_le_of_lt below beyond), smul_zero]

end
end D5.S3.VertexAlgebra.LatticeSugawaraLocalNilpotence
