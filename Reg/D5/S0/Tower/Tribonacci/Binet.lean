import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.D5.S3.Geometry.Rauzy.Interior

/-! Norm observations of the two secondary Tribonacci roots. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S0.Tower.Tribonacci.Binet

open _root_.D5.S0.Tower.Tribonacci.Binet
open _root_.D5.S0.Tower.Tribonacci.Values
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ tribonacciCharacteristicPolynomial.roots →
    z ≠ (tribonacciConstant : ℂ) →
      z + star z = ((1 - tribonacciConstant : ℝ) : ℂ) ∧
      z * star z = ((tribonacciConstant ^ 2 - tribonacciConstant - 1 : ℝ) : ℂ) ∧
      tribonacciConstant * (R.readout () () z) ^ 2 = 1

abbrev sourceScope := type_of% (@tribonacci_secondary_root_relations)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := (h Reg.D5.S3.Geometry.Rauzy.Interior.root_mem tribonacciSecondaryRoot.2.2.1).2.2
  norm_num [erased, realize] at hh

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@tribonacci_secondary_root_relations, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change ‖(0 : ℂ)‖ ≠ ‖(1 : ℂ)‖
    norm_num

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@tribonacci_secondary_root_relations) (Realization signature) Unit Unit where
  unitName := `D5.S0.Tower.Tribonacci.Binet.tribonacci_secondary_root_relations.__information_unit
  realizationName := `Reg.D5.S0.Tower.Tribonacci.Binet.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => ‖z‖) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S0.Tower.Tribonacci.Binet
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "fn", "arg", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S0.Tower.Tribonacci.Binet
