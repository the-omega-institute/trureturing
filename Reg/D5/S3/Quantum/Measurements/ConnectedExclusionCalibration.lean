import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurements.ConnectedExclusionCalibration
import Reg.Support.DependentFamily

/-! The original transition probability is observed over its complete source family. -/

namespace Reg.D5.S3.Quantum.Measurements.ConnectedExclusionCalibration

open _root_.D5.S3.Quantum.Measurements.ConnectedExclusionCalibration
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

structure Parameters where
  Vertex : Type u
  finiteVertex : Fintype Vertex
  decideVertex : DecidableEq Vertex
  configurations : Finset (Finset Vertex)
  response : configurations → configurations → ℝ
  output : configurations

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := p.configurations
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p s => p.response p.output s) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => (2 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (G : SimpleGraph V) (S : Finset (Finset V)) (_hS : IsRecordFamily G S)
    (T : S → S → ℝ) (a b : V → ℝ) (_hT : ResponseLaws S T a b)
    (_hG : G.Connected) (_hseed : ∃ k, a k = 0),
    (∀ k, a k = 0 ∧ b k = 1) ∧ ∀ t s,
      r.readout () ⟨V, fv, dv, S, T, t⟩ s = if t = s then 1 else 0

theorem actual_law : arena.{u}.Law actual := by
  exact @connected_response_calibration

abbrev SampleVertex := ULift.{u} Unit
abbrev sampleFamily : Finset (Finset SampleVertex.{u}) := Finset.univ

def sampleResponse (t s : sampleFamily.{u}) : ℝ := if t = s then 1 else 0

private theorem sample_family : IsRecordFamily (⊥ : SimpleGraph SampleVertex.{u})
    sampleFamily := by
  refine ⟨Finset.mem_univ _, fun k => Finset.mem_univ _, ?_⟩
  intro t _
  rw [SimpleGraph.isIndepSet_iff]
  intro i _ j _ _
  simp

private theorem sample_laws : ResponseLaws sampleFamily.{u} sampleResponse
    (fun _ => 0) (fun _ => 1) := by
  constructor
  · intro t s
    unfold sampleResponse
    split_ifs <;> norm_num
  · intro s
    simp [sampleResponse]
  · intro k s
    unfold marginal
    rw [Fintype.sum_eq_single s]
    · simp [sampleResponse]
    · intro t hne
      simp [sampleResponse, hne]
  · intro _ _
    rfl

private theorem sample_connected : (⊥ : SimpleGraph SampleVertex.{u}).Connected := by
  constructor
  intro i j
  have h : i = j := Subsingleton.elim _ _
  subst j
  exact .rfl

def emptyRecord : sampleFamily.{u} := ⟨∅, Finset.mem_univ _⟩
def singletonRecord : sampleFamily.{u} := ⟨{ULift.up ()}, Finset.mem_univ _⟩

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := (h (⊥ : SimpleGraph SampleVertex.{u}) sampleFamily sample_family
    sampleResponse (fun _ => 0) (fun _ => 1) sample_laws sample_connected
    ⟨ULift.up (), rfl⟩).2 emptyRecord emptyRecord
  norm_num [rejected, realize] at hh

def source_registration : Registration arena.{u}
    (type_of% @connected_response_calibration.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    refine ⟨⟨SampleVertex, inferInstance, inferInstance, sampleFamily,
      sampleResponse, emptyRecord⟩, emptyRecord, singletonRecord, ?_⟩
    norm_num [actual, realize, sampleResponse, emptyRecord, singletonRecord]

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@connected_response_calibration.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Measurements.ConnectedExclusionCalibration.unit
  realizationName := `Reg.D5.S3.Quantum.Measurements.ConnectedExclusionCalibration.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p s => p.response p.output s) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurements.ConnectedExclusionCalibration
    definition := none
    coordinates := #[0, 1, 2, 4, 6, 12]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "arg", "body", "body", "fn", "arg"]
      stateBinder := 13
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Measurements.ConnectedExclusionCalibration
