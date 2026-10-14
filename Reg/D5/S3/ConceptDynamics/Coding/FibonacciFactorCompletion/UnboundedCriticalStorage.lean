import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open _root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.ExactOriginal206
noncomputable section
universe u_1
open UnboundedCriticalStorage UnboundedReturnCount Operations Bilateral
open _root_.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

abbrev observationSignature : Signature.{u_1+1,u_1,0,0,0} where
  Params := Σ _ : Type u_1, ℕ
  State := fun p => Frame p.1 Label
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ := fun _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization observationSignature :=
  realize.{u_1+1,u_1,0,0,0} observationSignature (fun _ _ t => t.output.length) (fun e => nomatch e)
def rejected : Realization observationSignature :=
  realize.{u_1+1,u_1,0,0,0} observationSignature (fun _ p _ => p.2 + 1) (fun e => nomatch e)

abbrev sourceArena : Arena.{u_1+1,u_1,0,0,0} where
  signature := observationSignature
  Law R := ∀ {Configuration : Type u_1}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (contract : Contract)
    (processing : Processing action initialConfiguration (OperationRecord o lam contract))
    (safety : ∀ a r, OperationRecord o lam contract a r → ∀ t,
      Run action (full r) ⟨initialConfiguration, 0, []⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p)
    (liveness : ∀ a r, OperationRecord o lam contract a r → OperationFiniteSource a → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration, 0, []⟩ t ∧ p < R.readout () ⟨Configuration, p⟩ t)
    (encoding : Configuration → List Bool)
    (faithful : Set.InjOn encoding {c | ∃ H,
      ReachThrough action initialConfiguration (OperationRecord o lam contract) H c}) ,
    ∀ N B : ℕ, Peak action initialConfiguration (OperationRecord o lam contract) encoding N
      ≤ (B : WithTop ℕ) → alphaInfinity*(N : ℝ)-107*alphaInfinity-1 ≤ (B : ℝ)

theorem stopped_run_eq {C : Type u_1} {input : ℕ → Option Color}
    {s t : Frame C Label} (h : Run (fun _ => .stopped) input s t) : t = s := by
  obtain ⟨vertices, trace⟩ := h
  induction trace with
  | refl => rfl
  | tail htrace edge ih => cases edge <;> contradiction

theorem rejected_law : ¬ sourceArena.{u_1}.Law rejected := by
  intro h
  let C := ULift.{u_1} Unit
  let c : C := ⟨()⟩
  let action : C → Op C Color Label := fun _ => .stopped
  have processing : Processing action c (OperationRecord (fun _ => false) lam .closed) := by
    refine ⟨⟨⟨c, 0, []⟩, ⟨_, .refl⟩, Or.inl rfl⟩, ?_⟩
    intro a r hr x y q o w f run impossible
    cases impossible
  have safety : ∀ a r, OperationRecord (fun _ => false) lam .closed a r → ∀ t,
      Run action (full r) ⟨c, 0, []⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = a p := by
    intro a r hr t run p hp
    have eq := stopped_run_eq run
    subst t
    simp at hp
  have live : ∀ a r, OperationRecord (fun _ => false) lam .closed a r →
      OperationFiniteSource a → ∀ p, ∃ t,
      Run action (full r) ⟨c, 0, []⟩ t ∧ p < rejected.readout () ⟨C, p⟩ t := by
    intro a r hr hf p
    exact ⟨⟨c, 0, []⟩, ⟨_, .refl⟩, Nat.lt_succ_self p⟩
  have faithful : Set.InjOn (fun _ : C => ([] : List Bool))
      {c' | ∃ H, ReachThrough action c (OperationRecord (fun _ => false) lam .closed) H c'} := by
    intro x hx y hy eq
    exact Subsingleton.elim x y
  have apos := actual_count_log_bounds.1
  obtain ⟨N, hN⟩ := exists_nat_gt ((107 * alphaInfinity + 1) / alphaInfinity)
  have large : 107 * alphaInfinity + 1 < alphaInfinity * (N : ℝ) := by
    have hh := (div_lt_iff₀ apos).mp hN
    simpa only [mul_comm] using hh
  have peak : Peak action c (OperationRecord (fun _ => false) lam .closed)
      (fun _ => []) N ≤ (0 : WithTop ℕ) := by
    exact iSup_le fun _ => iSup_le fun _ => le_rfl
  have impossible := @h C action c (fun _ => false) .closed processing safety live
    (fun _ => []) faithful N 0 peak
  norm_num at impossible
  linarith

def evidence : Registration sourceArena.{u_1} (type_of% @D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.critical_decoder_storage.{u_1}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.critical_decoder_storage.{u_1}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨ULift.{u_1} Unit, 0⟩, ⟨⟨()⟩, 0, []⟩, ⟨⟨()⟩, 0, [.L0]⟩, ?_⟩
    norm_num [actual, realize]

def critical_decoder_storage_registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,u_1+1,u_1,0,0,0,0}
      (@_root_.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.critical_decoder_storage.{u_1})
      (type_of% (realize.{u_1+1,u_1,0,0,0} observationSignature
        (fun _ _ t => t.output.length) (fun e => nomatch e))) Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.ExactOriginal206.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.ExactOriginal206.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨sourceArena.{u_1}⟩
  objectArena := .source ⟨sourceArena.{u_1}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source sourceArena.{u_1} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize.{u_1+1,u_1,0,0,0} observationSignature
    (fun _ _ t => t.output.length) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage
    definition := none
    coordinates := #[0, 11]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "domain", "body", "body", "body", "body", "body", "arg", "body", "arg", "arg"]
      stateBinder := 12
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms critical_decoder_storage_registration
end
end Reg.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.UnboundedCriticalStorage.ExactOriginal206
