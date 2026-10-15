import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure

namespace Reg.D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure

open Set Filter _root_.Topology Cardinal
open _root_.D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure
open _root_.D5.S3.ConceptDynamics.InformationEscape

/- The dependent parameters retain arbitrary source types and all original operands.
The raw source-selection reconstruction is not asserted by these family proofs. -/

def signature (P : Type 1) (State : P → Type) : DependentFamily.Signature where
  Params := P
  State := State
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual {P : Type 1} {State : P → Type} (certificate : ∀ p, State p → Prop) :
    DependentFamily.Realization (signature P State) :=
  DependentFamily.realize (signature P State) (fun _ p x => certificate p x) (fun a => nomatch a)

def arena {P : Type 1} (State : P → Type) (premise : P → Prop) : DependentFamily.Arena where
  signature := signature P State
  Law := fun r => ∀ p, premise p → ∃ x, r.readout () p x

def familyEvidence {P : Type 1} {State : P → Type} (premise : P → Prop)
    (certificate : ∀ p, State p → Prop) {source : Prop}
    (bridge : source ↔ ∀ p, premise p → ∃ x, certificate p x) (positive : source)
    (pzero : P) (hzero : premise pzero)
    (pvar : P) (x y : State pvar) (hx : certificate pvar x) (hy : ¬ certificate pvar y) :
    DependentFamily.Registration (arena State premise) source := by
  let rejected : DependentFamily.Realization (signature P State) :=
    DependentFamily.realize (signature P State) (fun _ _ _ => False) (fun a => nomatch a)
  have bad : ¬ (arena State premise).Law rejected := by
    intro h
    obtain ⟨_, hfalse⟩ := h pzero hzero
    exact hfalse
  refine ⟨actual certificate, bridge, ⟨bridge.mp positive, rejected, bad⟩, ?_, ?_⟩
  · constructor
    · intro i
      refine ⟨rejected, ?_, rfl, bad⟩
      intro j hji
      exact False.elim (hji (@Subsingleton.elim Unit inferInstance j i))
    · intro a
      exact Empty.elim a
  · intro i
    refine ⟨pvar, x, y, ?_⟩
    intro h
    change certificate pvar x = certificate pvar y at h
    exact hy (h ▸ hx)

namespace FreshChoice

structure Inputs where
  X : Type
  B : Type
  I : Type
  q : X → B
  A : I → Set X
  H : Set X

def premise (p : Inputs) : Prop :=
  #p.I ≤ 𝔠 ∧ #p.H ≤ 𝔠 ∧
    ∀ i (F : Set p.B), #F ≤ 𝔠 → ∃ x ∈ p.A i, p.q x ∉ F

def certificate (p : Inputs) (f : p.I → p.X) : Prop :=
  (∀ i, f i ∈ p.A i) ∧ Function.Injective (p.q ∘ f) ∧
    ∀ i, p.q (f i) ∉ p.q '' p.H

abbrev sourceScope := type_of% (@exists_fresh_choice)

theorem bridge : sourceScope ↔ ∀ p : Inputs, premise p → ∃ f, certificate p f := by
  constructor
  · intro h p hp
    exact h p.q p.A p.H hp.1 hp.2.1 hp.2.2
  · intro h X B I q A H hI hH hs
    exact h ⟨X, B, I, q, A, H⟩ ⟨hI, hH, hs⟩

def zero : Inputs := ⟨Empty, Empty, Empty, id, (fun i => nomatch i), ∅⟩

theorem zero_premise : premise zero := by
  refine ⟨?_, ?_, ?_⟩
  · exact (show #Empty ≤ 𝔠 from mk_le_aleph0.trans aleph0_le_continuum)
  · change #(∅ : Set Empty) ≤ 𝔠
    exact (mk_subtype_le _).trans
      (show #Empty ≤ 𝔠 from mk_le_aleph0.trans aleph0_le_continuum)
  · intro i
    exact Empty.elim i

def varying : Inputs := ⟨Bool, Bool, Unit, id, (fun _ => {true}), ∅⟩

def evidence : DependentFamily.Registration
    (arena (fun p : Inputs => p.I → p.X) premise) sourceScope :=
  familyEvidence premise certificate bridge (@exists_fresh_choice) zero zero_premise
    varying (fun _ => true) (fun _ => false)
    (by
      change (∀ i : Unit, true ∈ ({true} : Set Bool)) ∧ _
      refine ⟨fun _ => mem_singleton _,
        (fun i j _ => @Subsingleton.elim Unit inferInstance i j), ?_⟩
      intro i h
      obtain ⟨x, hx, _⟩ := h
      exact hx)
    (by
      intro h
      have bad : false ∈ ({true} : Set Bool) := h.1 ()
      exact Bool.false_ne_true (mem_singleton_iff.mp bad))

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_fresh_choice) (DependentFamily.Realization (signature Inputs (fun p => p.I → p.X)))
      (Type 1) Unit where
  unitName :=
    `D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure.exists_fresh_choice.__information_unit
  realizationName :=
    `Reg.D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure.FreshChoice.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena (fun p : Inputs => p.I → p.X) premise⟩
  objectArena := .source ⟨arena (fun p : Inputs => p.I → p.X) premise⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (arena (fun p : Inputs => p.I → p.X) premise) ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize (signature Inputs (fun p => p.I → p.X))
    (fun _ p f => certificate p f) (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some Type
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end FreshChoice

namespace Closure

structure Inputs where
  X : Type
  B : Type
  top : TopologicalSpace X
  t1 : @T1Space X top
  good : Set X
  q : X → B
  seed : Set X

def premise (p : Inputs) : Prop :=
  letI := p.top
  FreshClusterSupply p.good p.q ∧ p.seed ⊆ p.good ∧ #p.seed ≤ 𝔠 ∧ InjOn p.q p.seed

def certificate (p : Inputs) (S : Set p.X) : Prop :=
  letI := p.top
  p.seed ⊆ S ∧ S ⊆ p.good ∧ #S ≤ 𝔠 ∧ InjOn p.q S ∧ IsCountablyCompact S

abbrev sourceScope := type_of% (@exists_countablyCompact_injOn_extension)

theorem bridge : sourceScope ↔ ∀ p : Inputs, premise p → ∃ S, certificate p S := by
  constructor
  · intro h p hp
    let := p.top
    let := p.t1
    exact h p.good p.q hp.1 p.seed hp.2.1 hp.2.2.1 hp.2.2.2
  · intro h X B top t1 good q hs seed hg hc hi
    exact h ⟨X, B, top, t1, good, q, seed⟩ ⟨hs, hg, hc, hi⟩

def zero : Inputs := ⟨Empty, Empty, ⊥, inferInstance, ∅, id, ∅⟩

theorem zero_premise : premise zero := by
  refine ⟨?_, subset_rfl, ?_, Function.injective_id.injOn⟩
  · intro e
    exact Empty.elim (e 0)
  · change #(∅ : Set Empty) ≤ 𝔠
    exact (mk_subtype_le _).trans
      (show #Empty ≤ 𝔠 from mk_le_aleph0.trans aleph0_le_continuum)

def varying : Inputs := ⟨Bool, Bool, ⊥, inferInstance, univ, id, {true}⟩

def evidence : DependentFamily.Registration
    (arena (fun p : Inputs => Set p.X) premise) sourceScope :=
  familyEvidence premise certificate bridge (@exists_countablyCompact_injOn_extension)
    zero zero_premise varying {true} ∅
    (by
      let : TopologicalSpace Bool := ⊥
      change ({true} : Set Bool) ⊆ {true} ∧ ({true} : Set Bool) ⊆ univ ∧
        #({true} : Set Bool) ≤ 𝔠 ∧ InjOn id ({true} : Set Bool) ∧ IsCountablyCompact ({true} : Set Bool)
      refine ⟨subset_rfl, subset_univ _, ?_, Function.injective_id.injOn, isCountablyCompact_singleton⟩
      rw [mk_singleton]
      exact one_le_aleph0.trans aleph0_le_continuum)
    (by intro h; exact h.1 (mem_singleton true))

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, 0, 0, 0, 0}
      (@exists_countablyCompact_injOn_extension)
      (DependentFamily.Realization (signature Inputs (fun p => Set p.X))) (Type 1) Unit where
  unitName :=
    `D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure.exists_countablyCompact_injOn_extension.__information_unit
  realizationName :=
    `Reg.D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure.Closure.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena (fun p : Inputs => Set p.X) premise⟩
  objectArena := .source ⟨arena (fun p : Inputs => Set p.X) premise⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (arena (fun p : Inputs => Set p.X) premise) ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ trivial
  readout := some (DependentFamily.realize (signature Inputs (fun p => Set p.X))
    (fun _ p S => certificate p S) (fun a => nomatch a))
  variation := .evidence ⟨True.intro⟩ trivial
  sensitivity := .evidence ⟨True.intro⟩ trivial
  partialSensitivity := none
  escapeFrom := some Type
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end Closure
end Reg.D5.S3.Topology.CountablyCompact.InjectiveSelectorClosure
