import D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
import Reg.Support.UnitSixO.Common

/-! Readouts for the null screen and the chiral curvature coordinates. -/

open LeanInformationAudit Matrix Omega.BinaryQuarticSpinor
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz
open _root_.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
open _root_.Reg.Support.UnitSixO (operandSignature)

namespace Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindPetrov% " result:ident familyName:term:max a:term:max family:term:max
    head:ident reads:term:max : term => do
  let owner := `D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
  let unit := owner ++ result.getId ++ `__information_unit
  `({ unitName := $(Lean.quote unit)
      realizationName := $familyName
      realizationSource := none
      generated := false
      arena := .source ⟨$a⟩
      objectArena := .source ⟨$a⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $a ⟨$family⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some (unitObserve% $head)
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
        definition := none
        coordinates := #[]
        readouts := $reads }
      continuation := .unknown
      familyRecord := none
      options := #[] })

macro "petrovRead% " result:ident head:ident occurrence:num : term =>
  `({ path := unitPath% $result $head 0 $occurrence
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false })

private abbrev zeroMass := KerrSchildWeylDoubleCopy4D.schwarzschildWeyl 0 1
private abbrev unitMass := KerrSchildWeylDoubleCopy4D.schwarzschildWeyl 1 1

private theorem zeroMass_spinor : spinorOfWeyl zeroMass = psiD 0 := by
  simpa using (petrov_coulomb_and_wave_spinors 0 1 0).1

private theorem unitMass_spinor : spinorOfWeyl unitMass = psiD 4 := by
  simpa using (petrov_coulomb_and_wave_spinors 1 1 0).1

private theorem unitMass_tide : WeylNullScreen.complexTide unitMass.val (some 1) = 24 := by
  rw [← weyl_spinor_null_screen, unitMass_spinor]
  norm_num [weylSpinorForm, weylEntry, Fin.sum_univ_two, psiD]

abbrev SpinorSignature : Signature := operandSignature WeylNullScreen.Weyl4 Coefficients

private theorem spinor_dependence : ∃ p x y,
    (unitObserve% spinorOfWeyl : Realization SpinorSignature).readout () p x ≠
      (unitObserve% spinorOfWeyl : Realization SpinorSignature).readout () p y := by
  refine ⟨(), zeroMass, unitMass, fun h => ?_⟩
  change spinorOfWeyl zeroMass = spinorOfWeyl unitMass at h
  rw [zeroMass_spinor, unitMass_spinor] at h
  have h2 := congrFun h 2
  norm_num [psiD] at h2

namespace Screen

abbrev signature : Signature := operandSignature Coefficients (Spinor → Spinor → Spinor →
  Spinor → ℂ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (C : WeylNullScreen.Weyl4) (z : ℂ),
    R.readout () () (spinorOfWeyl C) ![z, 1] ![z, 1] ![z, 1] ![z, 1] =
      WeylNullScreen.complexTide C.val (some z)

def family : Registration arena (type_of% (@weyl_spinor_null_screen)) :=
  unitFamily% arena (@weyl_spinor_null_screen) (unitObserve% weylSpinorForm)
    (unitObserve% (fun _ _ _ _ _ => 0))
    (by
      intro h
      have ht := h unitMass 1
      rw [unitMass_tide] at ht
      change (0 : ℂ) = 24 at ht
      norm_num at ht)
    (by
      refine ⟨(), psiD 0, psiD 4, fun h => ?_⟩
      let t : Spinor := ![1, 1]
      have ht := congrFun (congrFun (congrFun (congrFun h t) t) t) t
      change weylSpinorForm (psiD 0) t t t t = weylSpinorForm (psiD 4) t t t t at ht
      norm_num [weylSpinorForm, weylEntry, Fin.sum_univ_two, psiD, t] at ht)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weyl_spinor_null_screen) (Realization signature) Unit Unit :=
  bindPetrov% weyl_spinor_null_screen
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov.Screen.family arena family
    weylSpinorForm #[petrovRead% weyl_spinor_null_screen weylSpinorForm 0]

end Screen

namespace Canonical

abbrev arena : Arena where
  signature := SpinorSignature
  Law R := ∀ M r A : ℝ,
    R.readout () () (KerrSchildWeylDoubleCopy4D.schwarzschildWeyl M r) =
      psiD (4 * (M / r ^ 3 : ℝ)) ∧
    sl2cAct (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)
      (spinorOfWeyl (PerturbedCausalOrderWeyl4D.waveWeyl A)) = psiN (-4 * (A : ℂ))

def family : Registration arena (type_of% (@petrov_coulomb_and_wave_spinors)) :=
  unitFamily% arena (@petrov_coulomb_and_wave_spinors) (unitObserve% spinorOfWeyl)
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have he := congrFun (h 1 1 0).1 2
      change (0 : ℂ) = psiD (4 * (1 / 1 ^ 3 : ℝ)) 2 at he
      norm_num [psiD] at he)
    spinor_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@petrov_coulomb_and_wave_spinors) (Realization SpinorSignature) Unit Unit :=
  bindPetrov% petrov_coulomb_and_wave_spinors
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov.Canonical.family arena family
    spinorOfWeyl #[petrovRead% petrov_coulomb_and_wave_spinors spinorOfWeyl 0]

end Canonical

namespace Chiral

abbrev arena : Arena where
  signature := SpinorSignature
  Law R := ∀ (C : WeylNullScreen.Weyl4),
    let E := (WeylNullScreen.weyl_electric_magnetic_equiv C).1.val
    let B := (WeylNullScreen.weyl_electric_magnetic_equiv C).2.val
    let Q := fun i j => (E i j : ℂ) - Complex.I * (B i j : ℂ)
    R.readout () () C = ![2 * (Q 0 0 - Q 1 1) - 4 * Complex.I * Q 0 1,
      2 * Q 0 2 - 2 * Complex.I * Q 1 2, -2 * (Q 0 0 + Q 1 1),
      -2 * Q 0 2 - 2 * Complex.I * Q 1 2, 2 * (Q 0 0 - Q 1 1) + 4 * Complex.I * Q 0 1]

def family : Registration arena (type_of% (@weyl_spinor_electric_magnetic)) :=
  unitFamily% arena (@weyl_spinor_electric_magnetic) (unitObserve% spinorOfWeyl)
    (unitObserve% (fun _ => 0))
    (by
      intro h
      have hm := (weyl_spinor_electric_magnetic unitMass).trans (h unitMass).symm
      change spinorOfWeyl unitMass = 0 at hm
      rw [unitMass_spinor] at hm
      have he := congrFun hm 2
      norm_num [psiD] at he)
    spinor_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weyl_spinor_electric_magnetic) (Realization SpinorSignature) Unit Unit :=
  bindPetrov% weyl_spinor_electric_magnetic
    `Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov.Chiral.family arena family
    spinorOfWeyl #[petrovRead% weyl_spinor_electric_magnetic spinorOfWeyl 0]

end Chiral

end


end Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Petrov
