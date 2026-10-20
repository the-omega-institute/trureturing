import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
import Reg.Support.DependentFamily

/-! Source-bound audit of the all-prime CHSH graph degree. -/

namespace Reg.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity

open _root_.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the degree expression as the dimension varies. -/
abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ p => (2 * p - 1) * (p - 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain injectivity, projector laws, and the full all-prime neighbour-count identity. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ (p : ℕ), ∀ [Fact p.Prime],
    Function.Injective (vertexProj p) ∧
      (∀ v, Matrix.trace (vertexProj p v) = 1 ∧
        vertexProj p v * vertexProj p v = vertexProj p v) ∧
      ∀ v,
        (Finset.univ.filter
          (fun w => w ≠ v ∧ vertexProj p v * vertexProj p w = 0)).card =
          r.readout () () p

theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbad := (law 2).2.2 (0, 0, 0)
  have hdegree := (result 2).2.2 (0, 0, 0)
  change (Finset.univ.filter
    (fun w => w ≠ (0, 0, 0) ∧ vertexProj 2 (0, 0, 0) * vertexProj 2 w = 0)).card = 0
    at hbad
  rw [hdegree] at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 2, 3, ?_⟩
  change (2 * 2 - 1) * (2 - 1) ≠ (2 * 3 - 1) * (3 - 1)
  norm_num

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
      (@_root_.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ _ p => (2 * p - 1) * (p - 1)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
      name := `D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.StabilizerCHSHGraphRegularity
