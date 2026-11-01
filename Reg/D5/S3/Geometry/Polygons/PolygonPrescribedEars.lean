import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.Polygons.PolygonPrescribedEars
import D5.S3.Geometry.Polygons.PolygonCompressionTrace

/-! The complete existential telescope with its actual complete-ear observation. -/

namespace Reg.D5.S3.Geometry.Polygons.PolygonPrescribedEars
open _root_.D5.S3.Geometry.Polygons
open PolygonEarSlide PolygonEarSlide.Carrier PolygonEarSlide.Actual PolygonEarContraction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

abbrev signature : Signature where
  Params := {n : ℕ // 14 ≤ n}
  State p := Finset (Sym2 (ZMod p.val))
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Finset (ZMod p.val)
  Anchor := Empty
  finiteAnchor := inferInstance

def readout (_ : Unit) (p : signature.Params) (T : signature.State p) :
    signature.Output () p := by
  letI : NeZero p.val := ⟨by have := p.property; omega⟩
  exact EarCenters T

def actual : Realization signature :=
  realize signature readout (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} [NeZero n] (hn : 14 ≤ n) (P : Finset (ZMod n)),
    Compatible P → 3 ≤ P.card → 6 ≤ n - P.card →
    ∃ T : Finset (Sym2 (ZMod n)),
      IsTriangulation T ∧ R.readout () ⟨n, hn⟩ T = P

private theorem sample_compatible : Compatible ({0, 2, 4} : Finset (ZMod 14)) := by
  intro i hi j hj _ hc
  have h := (PolygonCompressionTrace.cross_ear_iff_adjacent (by decide) i j).mp hc
  simp only [mem_insert, mem_singleton] at hi hj
  rcases hi with rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl <;> revert h <;> decide

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨T, _, he⟩ := h (n := 14) (by decide) {0, 2, 4} sample_compatible
    (by decide) (by decide)
  change (∅ : Finset (ZMod 14)) = {0, 2, 4} at he
  have h0 : (0 : ZMod 14) ∈ (∅ : Finset (ZMod 14)) := by rw [he]; simp
  simpa using h0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨14, by decide⟩, ∅, {ear (0 : ZMod 14)}, ?_⟩
  change EarCenters (∅ : Finset (Sym2 (ZMod 14))) ≠ EarCenters {ear (0 : ZMod 14)}
  intro h
  have hi : (0 : ZMod 14) ∈ EarCenters {ear (0 : ZMod 14)} := by simp
  rw [← h] at hi
  simp [EarCenters] at hi

def source_registration :
    Registration arena (type_of% @_root_.D5.S3.Geometry.Polygons.PolygonPrescribedEars.prescribed_complete_ears) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Geometry.Polygons.PolygonPrescribedEars.prescribed_complete_ears,
    rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact False.elim (hj (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration
    (@_root_.D5.S3.Geometry.Polygons.PolygonPrescribedEars.prescribed_complete_ears)
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Geometry.Polygons.PolygonPrescribedEars.unit
  realizationName := `Reg.D5.S3.Geometry.Polygons.PolygonPrescribedEars.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature readout (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.Polygons.PolygonPrescribedEars
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]}

end
end Reg.D5.S3.Geometry.Polygons.PolygonPrescribedEars
