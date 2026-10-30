import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
import Reg.Support.DependentFamily

/-! Source-bound audit of the codimension-one equality for the lazy two-causal face. -/

namespace Reg.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet

open _root_.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe equality on the two natural-number dimension operands. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Preserve validity and read the face dimension against the polytope dimension. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n →
    (∀ p ∈ twoCausalPolytope n, 0 ≤ jOne p) ∧
    R.readout () ()
      (Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n ∩ {p | jOne p = 0})) + 1)
      (Module.finrank ℝ (vectorSpan ℝ (twoCausalPolytope n)))

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 2 (by decide)).2

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hbad : (1 : ℕ) = 0 := Eq.mp (congrFun he 0) rfl
  exact Nat.one_ne_zero hbad

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
      name := `D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.LazyTwoCausalJOneFacet
