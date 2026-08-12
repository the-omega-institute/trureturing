/- GID: D5/S3/QuantumContext/PublicLedgerDescent
   generality: G
   mirror-B: D5/B/S3/QuantumContext/PublicLedgerDescent
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Public context valuations descend uniquely and retain their additive event laws. -/

/- Library-search audit trail (2026-08-12):
   * Searches of the repository and pinned mathlib tree for public-ledger gluing and
     context-independent valuation descent found no packaged theorem with this interface.
   * `Classical.choose` and `Classical.choose_spec` select a context containing a covered event;
     overlap compatibility makes that choice immaterial, and `Subtype.ext` proves uniqueness on
     the covered-event carrier.
   * `Finset.sum_union` is used only to certify the concrete finite witnesses' local event laws.
     It is not the descent theorem or its additivity conclusion.
   * The projection corollary imports the frozen eighteen-projection configuration and uses
     finite sets of its actual `ConfigurationProjection` values as coarse-grainable events.
-/

import D5.S3.QuantumContext.ProjectionValuationObstruction

/-!
# Public ledger descent

A context family is public when overlapping contexts assign the same value to the same event.
That compatibility is exactly what permits the local rows to glue to one valuation on all events
presented by at least one context. If the local rows obey an explicit event-decomposition law, the
unique global valuation obeys the same law on every context. Conversely, a single global row whose
restrictions recover the local rows forces both overlap compatibility and those additive laws.

This is the pre-Gleason descent step only. It assumes the local additive valuation law and proves
that the law is noncontextual; it asserts no positivity, representation, or Born-rule uniqueness.
-/

namespace D5.S3.QuantumContext.PublicLedgerDescent

/-- Events presented by at least one context. Restricting the carrier to covered events is what
makes the descended valuation unique without assigning arbitrary values outside the experiment. -/
abbrev CoveredEvent {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) :=
  {e : Event // ∃ c, e ∈ support c}

/-- Publicness: every pair of contexts uses the same ledger entry for a shared event. -/
def IsPublic {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (localValue : Context → Event → ℝ) : Prop :=
  ∀ c d e, e ∈ support c → e ∈ support d → localValue c e = localValue d e

/-- A global valuation restricts to every local context row. -/
def RestrictsToContexts {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (localValue : Context → Event → ℝ)
    (globalValue : CoveredEvent support → ℝ) : Prop :=
  ∀ c e (he : e ∈ support c),
    globalValue ⟨e, ⟨c, he⟩⟩ = localValue c e

/-- Each local valuation is additive for the declared event decompositions available in its
context. For projection events, `decomposes whole left right` says that `whole` is the disjoint
coarse-graining of `left` and `right`. -/
def IsContextwiseAdditive {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (decomposes : Event → Event → Event → Prop)
    (localValue : Context → Event → ℝ) : Prop :=
  ∀ c whole left right,
    whole ∈ support c → left ∈ support c → right ∈ support c →
      decomposes whole left right →
        localValue c whole = localValue c left + localValue c right

/-- The one descended valuation satisfies every additive decomposition exposed by every context. -/
def IsGloballyAdditiveOnContexts {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (decomposes : Event → Event → Event → Prop)
    (globalValue : CoveredEvent support → ℝ) : Prop :=
  ∀ c whole left right
      (hwhole : whole ∈ support c) (hleft : left ∈ support c)
      (hright : right ∈ support c),
    decomposes whole left right →
      globalValue ⟨whole, ⟨c, hwhole⟩⟩ =
        globalValue ⟨left, ⟨c, hleft⟩⟩ + globalValue ⟨right, ⟨c, hright⟩⟩

/-- Publicness transports a coarse-graining price from the context displaying its pieces to any
other context displaying the unchanged coarse event. This is the explicit cross-context additive
law: its proof needs both publicness and the source context's valuation law. -/
theorem public_ledger_cross_context_additivity
    {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (decomposes : Event → Event → Event → Prop)
    (localValue : Context → Event → ℝ)
    (hPublic : IsPublic support localValue)
    (hAdditive : IsContextwiseAdditive support decomposes localValue) :
    ∀ c d whole left right,
      whole ∈ support c → left ∈ support c → right ∈ support c →
        whole ∈ support d → decomposes whole left right →
          localValue d whole = localValue c left + localValue c right := by
  intro c d whole left right hwhole hleft hright hwhole' hdecomposes
  calc
    localValue d whole = localValue c whole :=
      (hPublic c d whole hwhole hwhole').symm
    _ = localValue c left + localValue c right :=
      hAdditive c whole left right hwhole hleft hright hdecomposes

/-- A context family is public and contextwise additive exactly when it is the family of
restrictions of a unique global valuation on covered events, additive on every context. -/
theorem public_ledger_descent_iff
    {Context Event : Type*} [DecidableEq Event]
    (support : Context → Finset Event) (decomposes : Event → Event → Event → Prop)
    (localValue : Context → Event → ℝ) :
    IsPublic support localValue ∧ IsContextwiseAdditive support decomposes localValue ↔
      ∃! globalValue : CoveredEvent support → ℝ,
        RestrictsToContexts support localValue globalValue ∧
          IsGloballyAdditiveOnContexts support decomposes globalValue := by
  classical
  constructor
  · rintro ⟨hPublic, hLocalAdditive⟩
    let globalValue : CoveredEvent support → ℝ := fun e ↦
      localValue (Classical.choose e.property) e.1
    have hRestricts : RestrictsToContexts support localValue globalValue := by
      intro c e he
      exact hPublic (Classical.choose (show ∃ d, e ∈ support d from ⟨c, he⟩)) c e
        (Classical.choose_spec (show ∃ d, e ∈ support d from ⟨c, he⟩)) he
    have hGlobalAdditive :
        IsGloballyAdditiveOnContexts support decomposes globalValue := by
      intro c whole left right hwhole hleft hright hdecomposes
      rw [hRestricts c whole hwhole, hRestricts c left hleft, hRestricts c right hright]
      exact hLocalAdditive c whole left right hwhole hleft hright hdecomposes
    refine ⟨globalValue, ⟨hRestricts, hGlobalAdditive⟩, ?_⟩
    intro other hOther
    funext event
    rcases event with ⟨event, ⟨c, hevent⟩⟩
    exact ((hRestricts c event hevent).trans (hOther.1 c event hevent).symm).symm
  · rintro ⟨globalValue, ⟨hRestricts, hGlobalAdditive⟩, _⟩
    constructor
    · intro c d event hc hd
      let eventAtC : CoveredEvent support := ⟨event, ⟨c, hc⟩⟩
      let eventAtD : CoveredEvent support := ⟨event, ⟨d, hd⟩⟩
      have hSameEvent : eventAtC = eventAtD := Subtype.ext rfl
      calc
        localValue c event = globalValue eventAtC := (hRestricts c event hc).symm
        _ = globalValue eventAtD := congrArg globalValue hSameEvent
        _ = localValue d event := hRestricts d event hd
    · intro c whole left right hwhole hleft hright hdecomposes
      rw [← hRestricts c whole hwhole, ← hRestricts c left hleft,
        ← hRestricts c right hright]
      exact hGlobalAdditive c whole left right hwhole hleft hright hdecomposes

/-- A finite event is the disjoint coarse-graining of two finer finite events. -/
def IsDisjointUnion {Atom : Type*} [DecidableEq Atom]
    (whole left right : Finset Atom) : Prop :=
  Disjoint left right ∧ whole = left ∪ right

open D5.S3.QuantumContext.ProjectionValuationObstruction

/-- The actual projections occurring in one frozen four-slot measurement context. -/
noncomputable def projectionContextSupport (c : Fin 9) :
    Finset ConfigurationProjection :=
  Finset.univ.image fun k ↦ labeledProjection (contextRay c k)

/-- All finite projection events available within one frozen measurement context. -/
noncomputable def projectionEventSupport (c : Fin 9) :
    Finset (Finset ConfigurationProjection) := by
  classical
  exact (projectionContextSupport c).powerset

/-- Public additive valuations on finite events of the frozen projection contexts are exactly the
restrictions of one unique noncontextual valuation, additive for disjoint projection unions. -/
theorem projection_public_ledger_descent
    (localValue : Fin 9 → Finset ConfigurationProjection → ℝ) :
    IsPublic projectionEventSupport localValue ∧
        IsContextwiseAdditive projectionEventSupport IsDisjointUnion localValue ↔
      ∃! globalValue : CoveredEvent projectionEventSupport → ℝ,
        RestrictsToContexts projectionEventSupport localValue globalValue ∧
          IsGloballyAdditiveOnContexts projectionEventSupport IsDisjointUnion globalValue := by
  classical
  exact public_ledger_descent_iff projectionEventSupport IsDisjointUnion localValue

/-- Two distinct finite contexts sharing one atomic event. -/
def witnessAtomSupport : Bool → Finset (Fin 3)
  | false => {0, 1}
  | true => {1, 2}

/-- Every finite event contained in one witness context. -/
def witnessEventSupport (c : Bool) : Finset (Finset (Fin 3)) :=
  (witnessAtomSupport c).powerset

/-- Compatible atomic rows: the shared atom has value `1 / 3` in both contexts. -/
noncomputable def witnessAtomValue : Bool → Fin 3 → ℝ
  | false => ![2 / 3, 1 / 3, 0]
  | true => ![0, 1 / 3, 2 / 3]

/-- The local value of a finite event is the sum of its atomic ledger entries. -/
noncomputable def witnessLocalValue (c : Bool) (event : Finset (Fin 3)) : ℝ :=
  ∑ atom ∈ event, witnessAtomValue c atom

/-- The compatible pair is nontrivial: distinct overlapping normalized context rows satisfy their
local additive laws and descend uniquely to one noncontextual global event valuation. -/
theorem overlapping_context_ledger_witness :
    witnessAtomSupport false ≠ witnessAtomSupport true ∧
    witnessLocalValue false ≠ witnessLocalValue true ∧
    ({1} : Finset (Fin 3)) ∈ witnessEventSupport false ∩ witnessEventSupport true ∧
    (∀ c, witnessLocalValue c (witnessAtomSupport c) = 1) ∧
    IsPublic witnessEventSupport witnessLocalValue ∧
    IsContextwiseAdditive witnessEventSupport IsDisjointUnion witnessLocalValue ∧
    ∃! globalValue : CoveredEvent witnessEventSupport → ℝ,
      RestrictsToContexts witnessEventSupport witnessLocalValue globalValue ∧
        IsGloballyAdditiveOnContexts witnessEventSupport IsDisjointUnion globalValue := by
  have hPublic : IsPublic witnessEventSupport witnessLocalValue := by
    intro c d event hec hed
    simp only [witnessEventSupport, Finset.mem_powerset] at hec hed
    cases c <;> cases d
    · rfl
    · apply Finset.sum_congr rfl
      intro atom hatom
      have hc := hec hatom
      have hd := hed hatom
      fin_cases atom <;> simp [witnessAtomSupport, witnessAtomValue] at hc hd ⊢
    · apply Finset.sum_congr rfl
      intro atom hatom
      have hc := hec hatom
      have hd := hed hatom
      fin_cases atom <;> simp [witnessAtomSupport, witnessAtomValue] at hc hd ⊢
    · rfl
  have hAdditive :
      IsContextwiseAdditive witnessEventSupport IsDisjointUnion witnessLocalValue := by
    intro c whole left right _ _ _ hdecomposes
    rcases hdecomposes with ⟨hDisjoint, rfl⟩
    simpa [witnessLocalValue] using
      (Finset.sum_union hDisjoint :
        ∑ atom ∈ left ∪ right, witnessAtomValue c atom =
          (∑ atom ∈ left, witnessAtomValue c atom) +
            ∑ atom ∈ right, witnessAtomValue c atom)
  have hNormalized : ∀ c, witnessLocalValue c (witnessAtomSupport c) = 1 := by
    intro c
    cases c <;> simp [witnessLocalValue, witnessAtomSupport, witnessAtomValue] <;> norm_num
  have hDescent :=
    (public_ledger_descent_iff witnessEventSupport IsDisjointUnion witnessLocalValue).mp
      ⟨hPublic, hAdditive⟩
  refine ⟨by decide, ?_, by decide, hNormalized, hPublic, hAdditive, hDescent⟩
  intro hRows
  have hAtZero := congrFun hRows ({0} : Finset (Fin 3))
  norm_num [witnessLocalValue, witnessAtomValue] at hAtZero

/-- A second pair keeps both context rows normalized and locally additive but disagrees on the
shared atomic event. It cannot be the restriction of any global valuation. -/
noncomputable def incompatibleWitnessAtomValue : Bool → Fin 3 → ℝ
  | false => ![2 / 3, 1 / 3, 0]
  | true => ![0, 2 / 3, 1 / 3]

noncomputable def incompatibleWitnessLocalValue
    (c : Bool) (event : Finset (Fin 3)) : ℝ :=
  ∑ atom ∈ event, incompatibleWitnessAtomValue c atom

/-- Without publicness, even two overlapping, normalized, contextwise additive valuations need not
descend: the shared singleton would have to receive both `1 / 3` and `2 / 3`. -/
theorem incompatible_overlapping_contexts_do_not_descend :
    (∀ c, incompatibleWitnessLocalValue c (witnessAtomSupport c) = 1) ∧
    IsContextwiseAdditive witnessEventSupport IsDisjointUnion incompatibleWitnessLocalValue ∧
    ¬ ∃ globalValue : CoveredEvent witnessEventSupport → ℝ,
      RestrictsToContexts witnessEventSupport incompatibleWitnessLocalValue globalValue := by
  have hNormalized :
      ∀ c, incompatibleWitnessLocalValue c (witnessAtomSupport c) = 1 := by
    intro c
    cases c <;>
      simp [incompatibleWitnessLocalValue, witnessAtomSupport, incompatibleWitnessAtomValue] <;>
        norm_num
  have hAdditive :
      IsContextwiseAdditive witnessEventSupport IsDisjointUnion
        incompatibleWitnessLocalValue := by
    intro c whole left right _ _ _ hdecomposes
    rcases hdecomposes with ⟨hDisjoint, rfl⟩
    simpa [incompatibleWitnessLocalValue] using
      (Finset.sum_union hDisjoint :
        ∑ atom ∈ left ∪ right, incompatibleWitnessAtomValue c atom =
          (∑ atom ∈ left, incompatibleWitnessAtomValue c atom) +
            ∑ atom ∈ right, incompatibleWitnessAtomValue c atom)
  refine ⟨hNormalized, hAdditive, ?_⟩
  rintro ⟨globalValue, hRestricts⟩
  have hFalseMem : ({1} : Finset (Fin 3)) ∈ witnessEventSupport false := by decide
  have hTrueMem : ({1} : Finset (Fin 3)) ∈ witnessEventSupport true := by decide
  let sharedAtFalse : CoveredEvent witnessEventSupport :=
    ⟨{1}, ⟨false, hFalseMem⟩⟩
  let sharedAtTrue : CoveredEvent witnessEventSupport :=
    ⟨{1}, ⟨true, hTrueMem⟩⟩
  have hSameEvent : sharedAtFalse = sharedAtTrue := Subtype.ext rfl
  have hConflict :
      incompatibleWitnessLocalValue false {1} =
        incompatibleWitnessLocalValue true {1} := by
    calc
      incompatibleWitnessLocalValue false {1} = globalValue sharedAtFalse :=
        (hRestricts false {1} hFalseMem).symm
      _ = globalValue sharedAtTrue := congrArg globalValue hSameEvent
      _ = incompatibleWitnessLocalValue true {1} := hRestricts true {1} hTrueMem
  norm_num [incompatibleWitnessLocalValue, incompatibleWitnessAtomValue] at hConflict

end D5.S3.QuantumContext.PublicLedgerDescent
