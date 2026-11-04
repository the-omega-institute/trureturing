import Reg.D5.S3.Geometry.Rauzy.Interior
import D5.S3.Geometry.Rauzy.TribonacciNullBoundary

/-! Planar measure observations at the original Rauzy frontier. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Geometry.Rauzy.TribonacciNullBoundary

open _root_.D5.S0.Tower.Tribonacci
open _root_.D5.S3.Geometry.Rauzy.TribonacciNullBoundary
open _root_.D5.S3.Constants.Irrationality.TribonacciTraceLattice
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Set MeasureTheory

abbrev signature : Signature where
  Params := Unit
  State _ := Set ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ENNReal
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ s => volume s) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (Values.tribonacciConstant : ℂ) →
      R.readout () () (frontier (RauzyFractal.rauzyFractal z)) = 0

abbrev sourceScope := type_of% (@rauzyFractal_frontier_volume_zero)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h Reg.D5.S3.Geometry.Rauzy.Interior.root_mem
    tribonacciSecondaryRoot.2.2.1
  exact one_ne_zero he

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@rauzyFractal_frontier_volume_zero, erased, erased_fails⟩
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
    change volume (∅ : Set ℂ) ≠ volume (univ : Set ℂ)
    simpa using ((measure_univ_ne_zero.mpr (NeZero.ne volume)) :
      volume (univ : Set ℂ) ≠ 0).symm

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@rauzyFractal_frontier_volume_zero) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.TribonacciNullBoundary.rauzyFractal_frontier_volume_zero.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.TribonacciNullBoundary.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => volume s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Rauzy.TribonacciNullBoundary
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.Rauzy.TribonacciNullBoundary
