/- GID: D5/S3/ConceptDynamics/Spacetime/FiniteCausalPaths
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/FiniteCausalPaths
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Causal paths in an N event archive have length at most N minus one. -/

import D5.S0.History.Spacetime.ArchiveCarrier
import Mathlib.Order.RelSeries
import Mathlib.Order.RelClasses
import Mathlib.Logic.Relation
import Mathlib.Data.List.Chain

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.FiniteCausalPaths

open D5.S0.History.Spacetime.ArchiveCarrier

variable {d : Nat}

/-- The carrier's existing strict relation supplies Mathlib's order interface. -/
theorem strictOrder (a : Archive d) : IsStrictOrder a.Event a.causal where
  irrefl := a.irrefl
  trans := a.trans

abbrev PathSeries {α : Type} (r : α → α → Prop) := RelSeries {p : α × α | r p.1 p.2}

/-- The bridge to LTSeries uses exactly the archive's relation, not a time quotient. -/
theorem path_length_bound (a : Archive d) (p : PathSeries a.causal) :
    p.length ≤ a.events.card - 1 := by
  let := strictOrder a
  let := partialOrderOfSO a.causal
  have hh := LTSeries.length_lt_card (α := a.Event) p
  rw [Fintype.card_coe] at hh
  omega

theorem generator_series_bound (a : Archive d) {r : a.Event → a.Event → Prop}
    (hr : ∀ x y, r x y → a.causal x y) (p : PathSeries r) :
    p.length ≤ a.events.card - 1 :=
  path_length_bound a (p.ofLE (fun _ h => hr _ _ h))

/-- An explicit finite sequence represents every nonempty transitive-closure path. -/
theorem transGen_has_series (a : Archive d) {r : a.Event → a.Event → Prop}
    {x y : a.Event} (h : Relation.TransGen r x y) :
    ∃ p : PathSeries r, 0 < p.length ∧ p.head = x ∧ p.last = y := by
  obtain ⟨z, hxz, hzy⟩ := Relation.TransGen.head'_iff.mp h
  obtain ⟨l, hl, hy⟩ := List.exists_isChain_cons_of_relationReflTransGen hzy
  let p : PathSeries r :=
    RelSeries.fromListIsChain (x :: z :: l) (by simp) (.cons_cons hxz hl)
  refine ⟨p, by simp [p, RelSeries.fromListIsChain], by simp [p], ?_⟩
  rw [← RelSeries.getLast_toList]
  simpa [p] using hy

/-- For a subrelation of a legal archive, bounded paths characterize actual TransGen. -/
theorem transGen_iff_bounded_series (a : Archive d) {r : a.Event → a.Event → Prop}
    (hr : ∀ x y, r x y → a.causal x y) (x y : a.Event) :
    Relation.TransGen r x y ↔ ∃ p : PathSeries r,
      0 < p.length ∧ p.length ≤ a.events.card - 1 ∧ p.head = x ∧ p.last = y := by
  constructor
  · intro h
    obtain ⟨p, hp, hx, hy⟩ := transGen_has_series a h
    exact ⟨p, hp, generator_series_bound a hr p, hx, hy⟩
  · rintro ⟨p, hp, _, rfl, rfl⟩
    let q : PathSeries (Relation.TransGen r) := p.ofLE (fun _ h => .single h)
    have hq := q.rel_of_lt (i := 0) (j := Fin.last p.length) (by change 0 < p.length; exact hp)
    exact hq

end D5.S3.ConceptDynamics.Spacetime.FiniteCausalPaths
