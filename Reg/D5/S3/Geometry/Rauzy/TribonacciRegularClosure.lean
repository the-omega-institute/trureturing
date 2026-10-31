import Reg.D5.S3.Geometry.Rauzy.Interior
import D5.S3.Geometry.Rauzy.TribonacciRegularClosure

/-! Regular-interior observations retain the original two root hypotheses. -/

set_option autoImplicit false
noncomputable section

namespace Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure

open _root_.D5.S0.Tower.Tribonacci
open _root_.D5.S3.Geometry.Rauzy.TribonacciRegularClosure
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
  realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e)

def erased : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {z : ℂ}, z ∈ Binet.tribonacciCharacteristicPolynomial.roots →
    z ≠ (Values.tribonacciConstant : ℂ) →
      R.readout () () (RauzyFractal.rauzyFractal z) = RauzyFractal.rauzyFractal z

abbrev sourceScope := type_of% (@rauzyFractal_closure_interior)

theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

theorem erased_fails : ¬ arena.Law erased := by
  intro h
  have he := h Reg.D5.S3.Geometry.Rauzy.Interior.root_mem
    tribonacciSecondaryRoot.2.2.1
  have hn := RauzyFractal.rauzyFractal_nonempty tribonacciSecondaryRoot.1
  change (∅ : Set ℂ) = RauzyFractal.rauzyFractal tribonacciSecondaryRoot.1 at he
  rw [← he] at hn
  exact not_nonempty_empty hn

def family : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨@rauzyFractal_closure_interior, erased, erased_fails⟩
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
    change closure (interior (∅ : Set ℂ)) ≠ closure (interior (univ : Set ℂ))
    simpa using (Set.empty_ne_univ : (∅ : Set ℂ) ≠ univ)

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@rauzyFractal_closure_interior) (Realization signature) Unit Unit where
  unitName := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure.rauzyFractal_closure_interior.__information_unit
  realizationName := `Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s => closure (interior s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Rauzy.TribonacciRegularClosure
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Geometry.Rauzy.TribonacciRegularClosure
