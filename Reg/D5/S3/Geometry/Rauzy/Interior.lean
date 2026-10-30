import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Rauzy.TribonacciInterior
import D5.S3.Constants.Irrationality.TribonacciTraceLattice

/-! Interior observations for compact separated-cylinder systems. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Geometry.Rauzy.Interior

open _root_.D5.S3.Geometry.Rauzy.Interior
open _root_.D5.S3.Geometry.Rauzy.TribonacciInterior
open _root_.D5.S0.Tower.Tribonacci.Binet
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set

abbrev signature : Signature where
  Params := Unit
  State _ := Set ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Set ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => interior s) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

theorem root_mem : tribonacciSecondaryRoot.1 ∈ tribonacciCharacteristicPolynomial.roots := by
  have hp : tribonacciCharacteristicPolynomial ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (2 : ℂ)) h
    norm_num [tribonacciCharacteristicPolynomial] at he
  apply (Polynomial.mem_roots hp).mpr
  simpa [Polynomial.IsRoot, tribonacciCharacteristicPolynomial] using tribonacciSecondaryRoot.2.1

def system : SeparatedCylinderSystem :=
  tribonacciCylinderSystem root_mem tribonacciSecondaryRoot.2.2.1

abbrev arena : Arena where
  signature := signature
  Law R := ∀ S : SeparatedCylinderSystem, (R.readout () () S.carrier).Nonempty

abbrev sourceScope := type_of% (@interior_nonempty_of_separated_cylinders)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have hh := h system
  exact Set.not_nonempty_empty hh

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@interior_nonempty_of_separated_cylinders, erased, erased_fails⟩
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
    refine ⟨(), ∅, univ, ?_⟩
    change interior (∅ : Set ℂ) ≠ interior (univ : Set ℂ)
    simpa only [interior_empty, interior_univ] using (Set.empty_ne_univ : (∅ : Set ℂ) ≠ univ)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@interior_nonempty_of_separated_cylinders) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.Interior.interior_nonempty_of_separated_cylinders.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.Interior.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => interior s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Rauzy.Interior
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.Rauzy.Interior
