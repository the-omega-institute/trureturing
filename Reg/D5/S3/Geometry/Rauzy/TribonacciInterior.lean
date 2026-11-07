import Reg.D5.S3.Geometry.Rauzy.Interior

/-! Interior observations for the exact Tribonacci Rauzy closure. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Geometry.Rauzy.TribonacciInterior

open _root_.D5.S0.Tower.Tribonacci
open _root_.D5.S3.Geometry.Rauzy.TribonacciInterior
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set
open Reg.D5.S3.Geometry.Rauzy.Interior

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (Values.tribonacciConstant : ℂ) →
      (R.readout () () (RauzyFractal.rauzyFractal z)).Nonempty

abbrev sourceScope := type_of% (@rauzyFractal_interior_nonempty)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  exact Set.not_nonempty_empty (h root_mem tribonacciSecondaryRoot.2.2.1)

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@rauzyFractal_interior_nonempty, erased, erased_fails⟩
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
      (@rauzyFractal_interior_nonempty) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.TribonacciInterior.rauzyFractal_interior_nonempty.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.TribonacciInterior.family
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
    owner := `D5.S3.Geometry.Rauzy.TribonacciInterior
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.Rauzy.TribonacciInterior
