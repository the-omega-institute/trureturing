import D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection
import Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

/-! The whole source family with its actual latest-claim observation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection

open _root_.D5.S3.ConceptDynamics.DependencyTopology
open LegalLedgerFixedSet FiniteLedgerCorrection
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.ConceptDynamics.DependencyTopology.LegalLedgerFixedSet
  (testKernel emptyLedger)
open LeanInformationAudit

universe u v w x
noncomputable section
attribute [local instance] Classical.propDecidable

structure Source where
  Proposition : Type u
  Proof : Type v
  Axiom : Type w
  Model : Type x
  kernel : KernelData Proposition Proof Axiom Model
  chain : Chain kernel
  domain : Finset Proposition

abbrev signature : Signature where
  Params := Σ s : Source.{u,v,w,x}, ℕ × s.domain
  State p := Policy p.1.chain p.1.domain
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Label
  Anchor := Empty
  finiteAnchor := inferInstance

def observedConclusion {P : Type u} {Proof : Type v} {Ax : Type w} {Model : Type x}
    {k : KernelData P Proof Ax Model} {chain : Chain k} {D : Finset P}
    (policy : Policy chain D) (observed : ℕ → D → Label) : Prop :=
    (∀ p : D, (changes (chain := chain) p.val).Subsingleton) ∧
    (∀ p : D, (corrections policy p).Finite ∧ (corrections policy p).ncard ≤ 2) ∧
    (events policy).Finite ∧
    (events policy).ncard = (∑' t, (policy.selected t).card) ∧
    (∑' t, (policy.selected t).card) ≤ 2 * D.card ∧
    (∃ T, ∀ t, T ≤ t → ∀ p : D,
      state (chain.ledger t) p.val = state (chain.ledger T) p.val) ∧
    (∀ T, (∀ t, T ≤ t → ∀ p : D,
      state (chain.ledger t) p.val = state (chain.ledger T) p.val) →
      ∃ stop, stop ≤ T + D.card ∧ ∀ t, stop ≤ t → mismatches policy t = ∅) ∧
    (∀ t p, observed t p = policy.claim t p) ∧
    (∀ t, claimLog policy (t + 1) = claimLog policy t ++ batch policy t ∧
      (batch policy t).length = (policy.selected t).card ∧
      ((batch policy t).map Prod.fst).Nodup ∧
      ∀ p s, (p,s) ∈ batch policy t ↔
        p ∈ policy.selected t ∧ s = state (chain.ledger t) p.val)

abbrev arena : Arena where
  signature := signature.{u,v,w,x}
  Law obs := ∀ (s : Source.{u,v,w,x}) (policy : Policy s.chain s.domain),
    Consistent s.kernel → observedConclusion policy
      (fun t p => obs.readout () ⟨s,t,p⟩ policy)

def actual : Realization signature.{u,v,w,x} := realize signature
  (fun _ p policy => latest (claimLog policy p.2.1) p.2.2) (fun a => nomatch a)

def rejected : Realization signature.{u,v,w,x} := realize signature
  (fun _ _ _ => .unverified) (fun a => nomatch a)

def emptyChain : Chain (testKernel.{u,v,w,x} false) where
  ledger _ := emptyLedger _
  step _ := id
  admissible _ _ := ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ => rfl⟩
  next _ := rfl

def sampleSource : Source.{u,v,w,x} :=
  ⟨ULift Unit, ULift Unit, ULift Unit, ULift Unit, (testKernel false),
    emptyChain, {⟨()⟩}⟩

instance : Unique sampleSource.{u,v,w,x}.domain where
  default := ⟨⟨()⟩, Finset.mem_singleton_self _⟩
  uniq p := by
    apply Subtype.ext
    exact Finset.mem_singleton.mp p.property

private theorem sample_consistent : Consistent sampleSource.{u,v,w,x}.kernel := by
  rintro p ⟨⟨π,h,_⟩,_⟩
  change false = true at h
  cases h

private theorem sample_state (t : ℕ) (p : sampleSource.{u,v,w,x}.domain) :
    state (sampleSource.chain.ledger t) p.val = .open := by
  have absent (q : sampleSource.{u,v,w,x}.Proposition) :
      q ∉ Frozen (sampleSource.chain.ledger t) := by
    change q ∉ (∅ : Finset (ULift.{u} Unit))
    exact Finset.notMem_empty q
  rw [state, ite_eq_right (absent p.val), ite_eq_right (absent _)]

def quietPolicy : Policy sampleSource.{u,v,w,x}.chain sampleSource.domain where
  claim _ _ := .open
  selected _ := ∅
  mismatch_only _ _ h := (Finset.notMem_empty _ h).elim
  progress t h := by obtain ⟨p,hp⟩ := h; exact (hp (sample_state t p).symm).elim
  update t p := by simp

def correctingPolicy : Policy sampleSource.{u,v,w,x}.chain sampleSource.domain where
  claim t _ := if t = 0 then .unverified else .open
  selected t := if t = 0 then Finset.univ else ∅
  mismatch_only t p h := by
    by_cases ht : t = 0
    · subst t; rw [sample_state]; decide
    · simp [ht] at h
  progress t h := by
    by_cases ht : t = 0
    · subst t; exact ⟨default, Finset.mem_univ _⟩
    · obtain ⟨p,hp⟩ := h
      exact (hp (by simp [ht, sample_state])).elim
  update t p := by
    have hp : p = default := Subsingleton.elim _ _
    subst p
    by_cases ht : t = 0 <;> simp [ht, sample_state]

private theorem rejected_fails : ¬ arena.{u,v,w,x}.Law rejected := by
  intro h
  have he := (h sampleSource quietPolicy sample_consistent).2.2.2.2.2.2.2.1
  have bad := he 0 default
  change Label.unverified = Label.open at bad
  cases bad

private theorem actual_dependence : ObservationalDependence signature actual.{u,v,w,x} := by
  intro i
  refine ⟨⟨sampleSource,0,default⟩, quietPolicy, correctingPolicy, ?_⟩
  intro bad
  change latest (claimLog quietPolicy 0) _ = latest (claimLog correctingPolicy 0) _ at bad
  have huniv : (Finset.univ : Finset sampleSource.{u,v,w,x}.domain) = {default} := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact Subsingleton.elim _ _
  simp [latest, claimLog, quietPolicy, correctingPolicy, huniv] at bad

def family : Registration arena.{u,v,w,x}
    (type_of% @finite_ledger_correction.{u,v,w,x}) where
  actual := realize signature actual.readout actual.anchor
  bridge := by
    constructor
    · intro h s policy consistent
      exact h policy consistent
    · intro h P Proof Ax Model k chain D policy consistent
      exact h ⟨P,Proof,Ax,Model,k,chain,D⟩ policy consistent
  variation := ⟨fun _ _ consistent => finite_ledger_correction _ consistent,
    rejected, rejected_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_fails⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro a
      exact nomatch a
  dependence := actual_dependence

#print axioms family

def registration : Contract.Registration.{
    max (max (u + 1) (v + 1)) (max (w + 1) (x + 1)), 0, 1, 0, 0, 0,
    max (max (u + 1) (v + 1)) (max (w + 1) (x + 1)), u, 0, 0, 0, 0}
    (@finite_ledger_correction.{u,v,w,x}) (Realization signature.{u,v,w,x})
    Unit Unit where
  unitName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection.unit
  realizationName := `Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature actual.readout actual.anchor)
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection
    definition := none
    coordinates := #[0, 1, 2, 3, 4, 5, 6]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body",
        "arg","arg","arg","arg","arg","arg","arg","fn","arg","body","body","fn","arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end
end Reg.D5.S3.ConceptDynamics.DependencyTopology.FiniteLedgerCorrection
