import D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
import Reg.Support.UnitSixO.Common

/-! Dependent readouts for the trace, density, and spatial flux. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
open _root_.Reg.Support.UnitSixO (operandSignature)
open Omega.BinaryQuarticSpinor

namespace Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Energy

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

macro "bindEnergy% " theoremId:ident groupId:ident ar:term:max fam:term:max
    headId:ident : term => do
  let owner := `D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
  let unit := owner ++ theoremId.getId ++ `__information_unit
  let familyName :=
    (`Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Energy ++ groupId.getId ++ `family)
  `({ unitName := $(Lean.quote unit)
      realizationName := $(Lean.quote familyName)
      realizationSource := none
      generated := false
      arena := .source ⟨$ar⟩
      objectArena := .source ⟨$ar⟩
      catalog := Lean.Name.anonymous
      localNames := false
      realization := .source $ar ⟨$fam⟩
      correspondence := ⟨.evidence, .evidence⟩
      bundleNonempty := .absent
      readout := some (unitObserve% $headId)
      variation := .absent
      sensitivity := .absent
      partialSensitivity := none
      escapeFrom := none
      sourceSelection := some {
        owner := `D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D
        definition := none
        coordinates := #[]
        readouts := #[{
          path := unitPath% $theoremId $headId 0 0
          stateBinder := 0
          functionOperand := true
          stateOperand := none
          booleanPredicate := false }] }
      continuation := .unknown
      familyRecord := none
      options := #[] })

private theorem densityZero : superenergy (0 : Coefficients) = 0 :=
  (belRobinson_superenergy_positive_definite 0).2.2.mpr rfl

private theorem densityN : superenergy (psiN 1) = 1 := by
  rw [(belRobinson_typeN_and_typeD_flux 1).1]
  norm_num

private theorem densityDependence : superenergy (psiN 1) ≠ superenergy 0 := by
  rw [densityN, densityZero]
  norm_num

private theorem complexDependence : belRobinsonComplex (psiN 1) ≠ belRobinsonComplex 0 := by
  intro h
  have he := congrArg Complex.re (congrFun h ![coordinateVector 0, coordinateVector 0,
    coordinateVector 0, coordinateVector 0])
  exact densityDependence he

private theorem fluxDependence : superPoynting (psiN 1) ≠ superPoynting (psiN 0) := by
  intro h
  have he := congrFun h (2 : Fin 3)
  rw [(belRobinson_typeN_and_typeD_flux 1).2.1, (belRobinson_typeN_and_typeD_flux 0).2.1] at he
  norm_num at he

namespace Trace

abbrev signature : Signature := operandSignature Coefficients ((Fin 4 → V4) → ℂ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (ψ : Coefficients) (u : Fin 4 → V4) (i j : Fin 4), i ≠ j →
    ∑ μ, metricSign μ *
      (R.readout () () ψ
        (Function.update (Function.update u i (coordinateVector μ)) j (coordinateVector μ))).re = 0

def family : Registration arena (type_of% (@belRobinson_completely_traceless)) :=
  unitFamily% arena (@belRobinson_completely_traceless)
    (unitObserve% belRobinsonComplex)
    (unitObserve% (fun (_ : Coefficients) (_ : Fin 4 → V4) => (1 : ℂ)))
    (by
      intro h
      have he := h 0 0 0 1 (by decide)
      norm_num [realize, metricSign, Fin.sum_univ_four] at he)
    (by exact ⟨(), psiN 1, 0, complexDependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_completely_traceless) (Realization signature) Unit Unit :=
  bindEnergy% belRobinson_completely_traceless Trace arena family belRobinsonComplex
end Trace

namespace Density

abbrev signature : Signature := operandSignature Coefficients ℝ

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ψ : Coefficients,
    let w := R.readout () () ψ
    w = ‖ψ 0‖ ^ 2 + 4 * ‖ψ 1‖ ^ 2 + 6 * ‖ψ 2‖ ^ 2 + 4 * ‖ψ 3‖ ^ 2 + ‖ψ 4‖ ^ 2 ∧
    0 ≤ w ∧ (w = 0 ↔ ψ = 0)

def family : Registration arena (type_of% (@belRobinson_superenergy_positive_definite)) :=
  unitFamily% arena (@belRobinson_superenergy_positive_definite)
    (unitObserve% superenergy)
    (unitObserve% (fun (_ : Coefficients) => (0 : ℝ)))
    (by
      intro h
      have he := (h (psiN 1)).1
      norm_num [realize, psiN] at he)
    (by exact ⟨(), psiN 1, 0, densityDependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_superenergy_positive_definite) (Realization signature) Unit Unit :=
  bindEnergy% belRobinson_superenergy_positive_definite Density arena family superenergy
end Density

namespace Curvature

abbrev arena : Arena where
  signature := Density.signature
  Law R := ∀ C : _root_.D5.S3.Geometry.Lorentz.WeylNullScreen.Weyl4,
    let E := (_root_.D5.S3.Geometry.Lorentz.WeylNullScreen.weyl_electric_magnetic_equiv C).1.val
    let B := (_root_.D5.S3.Geometry.Lorentz.WeylNullScreen.weyl_electric_magnetic_equiv C).2.val
    R.readout () () (spinorOfWeyl C) = 16 * ((E * E).trace + (B * B).trace)

def family : Registration arena (type_of% (@belRobinson_electric_magnetic_density)) :=
  unitFamily% arena (@belRobinson_electric_magnetic_density)
    (unitObserve% superenergy)
    (unitObserve% (fun (_ : Coefficients) => (1 : ℝ)))
    (by
      intro h
      have he := h 0
      simp [realize] at he)
    (by exact ⟨(), psiN 1, 0, densityDependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_electric_magnetic_density) (Realization Density.signature) Unit Unit :=
  bindEnergy% belRobinson_electric_magnetic_density Curvature arena family superenergy
end Curvature

namespace Bound

abbrev signature : Signature := operandSignature Coefficients (Fin 3 → ℝ)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ ψ : Coefficients, let p := R.readout () () ψ
    p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 ≤ superenergy ψ ^ 2

def family : Registration arena (type_of% (@belRobinson_super_poynting_bound)) :=
  unitFamily% arena (@belRobinson_super_poynting_bound)
    (unitObserve% superPoynting)
    (unitObserve% (fun (_ : Coefficients) (_ : Fin 3) => (1 : ℝ)))
    (by
      intro h
      have he := h 0
      norm_num [realize, densityZero] at he)
    (by exact ⟨(), psiN 1, psiN 0, fluxDependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_super_poynting_bound) (Realization signature) Unit Unit :=
  bindEnergy% belRobinson_super_poynting_bound Bound arena family superPoynting
end Bound

namespace AlgebraicTypes

abbrev arena : Arena where
  signature := Bound.signature
  Law R := ∀ c : ℂ,
    let pN := R.readout () () (psiN c)
    let pD := R.readout () () (psiD c)
    superenergy (psiN c) = ‖c‖ ^ 2 ∧ pN = ![0, 0, -(‖c‖ ^ 2)] ∧
    Real.sqrt (pN 0 ^ 2 + pN 1 ^ 2 + pN 2 ^ 2) = superenergy (psiN c) ∧
    superenergy (psiD c) = 6 * ‖c‖ ^ 2 ∧ pD = 0

def family : Registration arena (type_of% (@belRobinson_typeN_and_typeD_flux)) :=
  unitFamily% arena (@belRobinson_typeN_and_typeD_flux)
    (unitObserve% superPoynting)
    (unitObserve% (fun (_ : Coefficients) (_ : Fin 3) => (0 : ℝ)))
    (by
      intro h
      have he := congrFun (h 1).2.1 (2 : Fin 3)
      norm_num [realize] at he)
    (by exact ⟨(), psiN 1, psiN 0, fluxDependence⟩)

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@belRobinson_typeN_and_typeD_flux) (Realization Bound.signature) Unit Unit :=
  bindEnergy% belRobinson_typeN_and_typeD_flux AlgebraicTypes arena family superPoynting
end AlgebraicTypes

end

end Reg.D5.S3.Geometry.Lorentz.PetrovBelRobinsonSuperenergy4D.Energy
