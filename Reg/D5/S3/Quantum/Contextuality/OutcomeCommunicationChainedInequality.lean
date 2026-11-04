import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
import Reg.Support.DependentFamily

/-! Source-bound audit of the relabelled chained value for finite COD models. -/

namespace Reg.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality

open _root_.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the chained value of a behaviour at its original number of inputs. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Fin n → Fin n → Fin 2 → Fin 2 → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ n p => chainedValue n p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Preserve oddness, every finite hidden-variable space, and all model hypotheses. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, Odd n → ∀ (α : Type) [Fintype α] (w : α → ℝ)
    (alice : Fin n → α → Fin 2 → ℝ) (bob : Fin n → α → Fin 2 → Fin 2 → ℝ),
    IsCODModel w alice bob → 1 ≤ R.readout () n (codBehaviour w alice bob)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hmodel : IsCODModel (n := 1) (α := Unit) (fun _ => 1)
      (fun _ _ _ => 1 / 2) (fun _ _ _ _ => 1 / 2) := by
    norm_num [IsCODModel, Fin.sum_univ_two]
  have hbad := h 1 (by decide) Unit (fun _ => 1)
    (fun _ _ _ => 1 / 2) (fun _ _ _ _ => 1 / 2) hmodel
  change (1 : ℝ) ≤ 0 at hbad
  norm_num at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, (fun _ _ _ _ => 0), (fun _ _ _ _ => 1), ?_⟩
  change chainedValue 1 (fun _ _ _ _ => 0) ≠ chainedValue 1 (fun _ _ _ _ => 1)
  norm_num [chainedValue, relabel, Fin.sum_univ_succ]

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
      (@_root_.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ n p => chainedValue n p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
    definition := some {
      owner := `D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
      name := `D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Contextuality.OutcomeCommunicationChainedInequality
