/- GID: D5/S3/ObserverMemory/Algorithms/UniformDescriptorDesign
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/UniformDescriptorDesign
   mirror-E: none(waiver:intermediate-synthesis-construction)
   anchors: []
   utility: none
   digest: Complete graph/type enumeration yields finite common-descriptor Valid Total Shared budget syntax. -/

import D5.S3.ObserverMemory.Algorithms.UniformDescriptorSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000

namespace D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign

open FirstOrder Language GuardedPhaseExecution UniformDescriptorPresentation
open UniformDescriptorSupport (dims descriptorTuple Valid Realizes literalProgram chosenLiterals H
  closeEx closeAll allF anyF realize_closeEx realize_closeAll realize_allF realize_anyF)

abbrev F (α : Type) := presburger.Formula α

variable {S Y : Type} {letters c charts types s q : Nat}
variable {Tsk : Task S Y letters c}

/-- One validity check for every installed read occurrence, including unreachable ones. -/
def ValidFormula (P : Presentation Tsk charts types) (G : Skeleton s c types) :
    F (Fin (blockTotal (dims P G))) :=
  allF (List.finRange G.readCount) fun a =>
    (P.valid (G.readKind a)).relabel (fun k => descriptorLayout (dims P G) ⟨a, k⟩)

/-- Source quantification follows the free common descriptor tuple. -/
def Total (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) : F (Fin (blockTotal (dims P G))) :=
  allF (List.finRange charts) fun η => closeAll
    (((P.adm η).relabel Sum.inr).imp (anyF G.halts fun h => H P M G η h))

/-- The two whole source tuples have separate tagged numeric blocks. Each H
binds its own terminal epoch and phase witnesses before the two rows are compared. -/
def Shared (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) : F (Fin (blockTotal (dims P G))) :=
  allF (List.finRange charts) fun η => allF (List.finRange charts) fun θ =>
    allF G.halts fun h => closeAll (closeAll (
      (((P.adm η).relabel (fun i => Sum.inl (Sum.inr i))) ⊓
       ((P.adm θ).relabel Sum.inr) ⊓
       ((H P M G η h).relabel Sum.inl) ⊓
       ((H P M G θ h).relabel
         (Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr))).imp
      ((P.same η θ).relabel (Sum.elim (fun i => Sum.inl (Sum.inr i)) Sum.inr))))

/-- The descriptor existential is outside every source, epoch and phase quantifier. -/
def Phi (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) : F (Fin 0) :=
  closeEx ((Total P M G ⊓ Shared P M G ⊓ ValidFormula P G).relabel Sum.inr)

/-- Actual closed finite Presburger syntax for every size one through K. -/
def Psi (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q) (K : Nat) : F (Fin 0) :=
  anyF (candidates K c types) fun candidate => Phi P M candidate.2

theorem valid_correct (P : Presentation Tsk charts types) (G : Skeleton s c types)
    (delta : Fin (blockTotal (dims P G)) → Nat) :
    (ValidFormula P G).Realize delta ↔ Valid P G delta := by
  simp only [ValidFormula, realize_allF, List.mem_finRange, forall_true_left,
    Valid]
  constructor <;> intro hv a
  · exact (Formula.realize_relabel (φ := P.valid (G.readKind a))
      (g := fun k => descriptorLayout (dims P G) ⟨a, k⟩) (v := delta)).mp (hv a)
  · exact (Formula.realize_relabel (φ := P.valid (G.readKind a))
      (g := fun k => descriptorLayout (dims P G) ⟨a, k⟩) (v := delta)).mpr (hv a)

private theorem total_formula (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat) :
    (Total P M G).Realize delta ↔ ∀ η n, (P.adm η).Realize n →
      ∃ h ∈ G.halts, (H P M G η h).Realize (Sum.elim delta n) := by
  simp only [Total, realize_allF, List.mem_finRange, forall_true_left,
    realize_closeAll, Formula.realize_imp, Formula.realize_relabel,
    Sum.elim_comp_inr, realize_anyF]

private theorem shared_formula (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat) :
    (Shared P M G).Realize delta ↔ ∀ η θ h, h ∈ G.halts → ∀ n m,
      (P.adm η).Realize n → (P.adm θ).Realize m →
      (H P M G η h).Realize (Sum.elim delta n) →
      (H P M G θ h).Realize (Sum.elim delta m) →
      (P.same η θ).Realize (Sum.elim n m) := by
  simp only [Shared, realize_allF, List.mem_finRange, forall_true_left,
    realize_closeAll, Formula.realize_imp, Formula.realize_inf, Formula.realize_relabel]
  constructor
  · intro law η θ h hh n m an am hη hθ
    have result := law η θ h hh n m
    have eη : Sum.elim (Sum.elim delta n) m ∘ Sum.inl = Sum.elim delta n := rfl
    have eθ : Sum.elim (Sum.elim delta n) m ∘
        Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr = Sum.elim delta m := by
      funext i; cases i <;> rfl
    have en : Sum.elim (Sum.elim delta n) m ∘ (fun i => Sum.inl (Sum.inr i)) = n := rfl
    have em : Sum.elim (Sum.elim delta n) m ∘ Sum.inr = m := rfl
    have es : Sum.elim (Sum.elim delta n) m ∘
        Sum.elim (fun i => Sum.inl (Sum.inr i)) Sum.inr = Sum.elim n m := by
      funext i; cases i <;> rfl
    simpa only [es] using result (by simpa only [en, em, eη, eθ] using ⟨⟨⟨an,am⟩,hη⟩,hθ⟩)
  · intro law η θ h hh n m assumptions
    have es : Sum.elim (Sum.elim delta n) m ∘
        Sum.elim (fun i => Sum.inl (Sum.inr i)) Sum.inr = Sum.elim n m := by
      funext i; cases i <;> rfl
    rw [es]
    apply law η θ h hh n m
    · exact assumptions.1.1.1
    · exact assumptions.1.1.2
    · exact assumptions.1.2
    · have eθ : Sum.elim (Sum.elim delta n) m ∘
          Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr = Sum.elim delta m := by
        funext i; cases i <;> rfl
      simpa only [eθ] using assumptions.2

/-- Eventuality includes a genuine halt endpoint; epochs may depend on the source. -/
def NativeTotal (G : Skeleton s c types) (literals : Fin G.readCount → Tsk.Literal) : Prop :=
  ∀ u : Tsk.Source, ∃ h J, G.program h = .halt ∧
    Run (literalProgram G literals) (Tsk.observation u) G.start Tsk.entryEpoch h J

/-- Shared compares every pair of original sources and their independent native
halt epochs. It certifies row constancy on a halt, not an arbitrary stored row. -/
def NativeShared (G : Skeleton s c types) (literals : Fin G.readCount → Tsk.Literal) : Prop :=
  ∀ (u v : Tsk.Source) h J J', G.program h = .halt →
    Run (literalProgram G literals) (Tsk.observation u) G.start Tsk.entryEpoch h J →
    Run (literalProgram G literals) (Tsk.observation v) G.start Tsk.entryEpoch h J' →
    Tsk.target u = Tsk.target v

/-- Exact formula semantics use all realizations. The disjoint chart bijection
supplies every original source and Same compares only admitted tuples. -/
theorem design_correct (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) (delta : Fin (blockTotal (dims P G)) → Nat)
    (hvalid : Valid P G delta) (literals : Fin G.readCount → Tsk.Literal)
    (hreal : Realizes P G delta literals) :
    ((ValidFormula P G).Realize delta ↔ Valid P G delta) ∧
    ((Total P M G).Realize delta ↔ NativeTotal G literals) ∧
    ((Shared P M G).Realize delta ↔ NativeShared G literals) := by
  refine ⟨valid_correct P G delta, ?_, ?_⟩
  · rw [total_formula]
    constructor
    · intro total u
      obtain ⟨⟨η, n, hn⟩, hu⟩ := P.theta_bijective.2 u
      obtain ⟨h, hh, reached⟩ := total η n hn
      obtain ⟨J, path⟩ := (UniformDescriptorSupport.native_support P M G η delta n hn
        hvalid literals hreal h 0).2.mp reached
      exact ⟨h, J, (Skeleton.mem_halts G h).mp hh, by simpa only [hu] using path⟩
    · intro total η n hn
      obtain ⟨h, J, hh, path⟩ := total (P.theta η ⟨n,hn⟩)
      exact ⟨h, (Skeleton.mem_halts G h).mpr hh,
        (UniformDescriptorSupport.native_support P M G η delta n hn hvalid literals hreal h 0).2.mpr
          ⟨J,path⟩⟩
  · rw [shared_formula]
    constructor
    · intro shared u v h J J' hh pu pv
      obtain ⟨⟨η, n, hn⟩, hu⟩ := P.theta_bijective.2 u
      obtain ⟨⟨θ, m, hm⟩, hv⟩ := P.theta_bijective.2 v
      have sh := shared η θ h ((Skeleton.mem_halts G h).mpr hh) n m hn hm
        ((UniformDescriptorSupport.native_support P M G η delta n hn hvalid literals hreal h 0).2.mpr
          ⟨J, by simpa only [hu] using pu⟩)
        ((UniformDescriptorSupport.native_support P M G θ delta m hm hvalid literals hreal h 0).2.mpr
          ⟨J', by simpa only [hv] using pv⟩)
      simpa only [hu,hv] using (P.same_exact η θ n m hn hm).mp sh
    · intro shared η θ h hh n m hn hm hη hθ
      obtain ⟨J, pu⟩ := (UniformDescriptorSupport.native_support P M G η delta n hn
        hvalid literals hreal h 0).2.mp hη
      obtain ⟨J', pv⟩ := (UniformDescriptorSupport.native_support P M G θ delta m hm
        hvalid literals hreal h 0).2.mp hθ
      exact (P.same_exact η θ n m hn hm).mpr
        (shared (P.theta η ⟨n,hn⟩) (P.theta θ ⟨m,hm⟩) h J J'
          ((Skeleton.mem_halts G h).mp hh) pu pv)

/-- Feasibility has no assumed installed outputs or solver contract. -/
def Feasible (P : Presentation Tsk charts types) (G : Skeleton s c types) : Prop :=
  ∃ delta, ∃ hv : Valid P G delta,
    NativeTotal G (chosenLiterals P G delta hv) ∧ NativeShared G (chosenLiterals P G delta hv)

theorem phi_correct (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q)
    (G : Skeleton s c types) :
    (Phi P M G).Realize (Fin.elim0 : Fin 0 → Nat) ↔ Feasible P G := by
  simp only [Phi, realize_closeEx, Formula.realize_relabel, Formula.realize_inf,
    Sum.elim_comp_inr]
  constructor
  · rintro ⟨delta, ⟨total,shared⟩,valid⟩
    have hv := (valid_correct P G delta).mp valid
    have real : Realizes P G delta (chosenLiterals P G delta hv) := by
      intro a; exact P.choose_mem _ _ _
    have exacts := design_correct P M G delta hv (chosenLiterals P G delta hv) real
    exact ⟨delta,hv,exacts.2.1.mp total,exacts.2.2.mp shared⟩
  · rintro ⟨delta,hv,total,shared⟩
    have real : Realizes P G delta (chosenLiterals P G delta hv) := by
      intro a; exact P.choose_mem _ _ _
    have exacts := design_correct P M G delta hv (chosenLiterals P G delta hv) real
    exact ⟨delta,⟨exacts.2.1.mpr total,exacts.2.2.mpr shared⟩,exacts.1.mpr hv⟩

private theorem candidates_sound {K c b : Nat}
    (candidate : Σ s, Skeleton (s+1) c b) (hm : candidate ∈ candidates K c b) :
    candidate.1+1 ≤ K := by
  simp only [candidates, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨s,hs,G,hG,he⟩ := hm
  cases he
  change s + 1 ≤ K
  simp only [List.mem_range] at hs
  omega

/-- This closes only arithmetic/native feasibility of complete typed candidates.
Output witness extraction and the original successful-table equivalence are separate obligations. -/
theorem budget_correct (P : Presentation Tsk charts types) (M : ReachedTransport Tsk q) (K : Nat) :
    (Psi P M K).Realize (Fin.elim0 : Fin 0 → Nat) ↔
      ∃ s, s+1 ≤ K ∧ ∃ G : Skeleton (s+1) c types, Feasible P G := by
  rw [Psi, realize_anyF]
  constructor
  · rintro ⟨candidate,hm,hp⟩
    exact ⟨candidate.1,candidates_sound candidate hm,candidate.2,
      (phi_correct P M candidate.2).mp hp⟩
  · rintro ⟨s,hs,G,hf⟩
    exact ⟨⟨s,G⟩,candidates_complete G hs,(phi_correct P M G).mpr hf⟩

#print axioms design_correct
#print axioms budget_correct

end D5.S3.ObserverMemory.Algorithms.UniformDescriptorDesign
