/- GID: D5/S3/ConceptDynamics/Spacetime/InactiveArchiveFibers
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/InactiveArchiveFibers
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Isolated inactive extensions give infinitely many historical classes with identical current data. -/

import D5.S3.ConceptDynamics.Spacetime.HistoricalEquivalence
import D5.S3.ConceptDynamics.Spacetime.ContextExtensionComplement

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Spacetime.InactiveArchiveFibers

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge HistoricalEquivalence

/-- Every rich history has an infinite family of isolated inactive extensions with
unchanged current and selected events and charges, and distinct historical isomorphism classes. -/
theorem infinite_fibre {d : Nat} (x : Rich d) :
    ∃ y : Nat → Rich d,
      (∀ k, ∃ j : ArchiveEmbedding x.1.archive (y k).1.archive,
        (∀ e, (j.eventMap e).val = e.val) ∧
        x.1.current.map j.eventMap = (y k).1.current ∧
        x.2.val.map j.eventMap = (y k).2.val ∧
        q (y k) = q x ∧ background (y k).1 = background x.1 ∧
        (y k).1.archive.events.card = x.1.archive.events.card + k ∧
        (∀ e : (y k).1.archive.Event, e.val ∉ x.1.archive.events →
          ∀ f, ¬ (y k).1.archive.causal e f ∧ ¬ (y k).1.archive.causal f e)) ∧
      Function.Injective y ∧
      (∀ i j, i ≠ j → ¬ HistoricalIso (y i) (y j)) := by
  classical
  let : Infinite HF := Infinite.of_injective natCode (fun _ _ h => natCode_inj.mp h)
  have fresh (k : Nat) : ∃ S : Finset HF,
      Disjoint x.1.archive.events S ∧ S.card = k := by
    obtain ⟨S, hS, hc⟩ := x.1.archive.events.finite_toSet.infinite_compl.exists_subset_card_eq k
    exact ⟨S, Finset.disjoint_left.mpr (fun e he hs => hS hs he), hc⟩
  choose S hS hc using fresh
  let a (k : Nat) : Archive d := {
    events := x.1.archive.events ∪ S k
    attributes := fun e => if h : e.val ∈ x.1.archive.events then
      x.1.archive.attributes ⟨e.val, h⟩ else
      { time := 0, position := fun _ => 0, positive := true, source := FreeMagma.of 0 }
    causal := fun e f => ∃ he : e.val ∈ x.1.archive.events,
      ∃ hf : f.val ∈ x.1.archive.events, x.1.archive.causal ⟨e.val, he⟩ ⟨f.val, hf⟩
    irrefl := by
      rintro e ⟨he, hf, h⟩
      exact x.1.archive.irrefl ⟨e.val, he⟩ h
    trans := by
      rintro e f g ⟨he, hf, hef⟩ ⟨_, hg, hfg⟩
      exact ⟨he, hg, x.1.archive.trans _ _ _ hef hfg⟩
    time_lt := by
      rintro e f ⟨he, hf, hef⟩
      simpa only [dif_pos he, dif_pos hf] using x.1.archive.time_lt _ _ hef }
  let j (k : Nat) : ArchiveEmbedding x.1.archive (a k) := {
    eventMap := {
      toFun := fun e => ⟨e.val, Finset.mem_union_left _ e.property⟩
      inj' := by
        intro e f h
        apply Subtype.ext
        exact congrArg (fun z : (a k).Event => z.val) h }
    attributes_eq := by
      intro e
      exact dif_pos e.property
    causal_iff := by
      intro e f
      constructor
      · rintro ⟨_, _, h⟩
        exact h
      · intro h
        exact ⟨e.property, f.property, h⟩ }
  let c (k : Nat) : Context d := ⟨a k, x.1.current.map (j k).eventMap⟩
  let y (k : Nat) : Rich d :=
    ⟨c k, ⟨x.2.val.map (j k).eventMap, Finset.map_subset_map.mpr x.2.property⟩⟩
  have hcard (k : Nat) : (y k).1.archive.events.card = x.1.archive.events.card + k := by
    change (x.1.archive.events ∪ S k).card = _
    rw [Finset.card_union_of_disjoint (hS k), hc k]
  let cj (k : Nat) : ContextExtensionComplement.ContextEmbedding x.1 (c k) := {
    archiveEmbedding := j k
    current_iff := fun _ => Finset.mem_map' _ }
  refine ⟨y, ?_, ?_, ?_⟩
  · intro k
    refine ⟨j k, fun _ => rfl, rfl, rfl, ContextExtensionComplement.map_charge (cj k) x.2.val,
      ContextExtensionComplement.map_charge (cj k) x.1.current, hcard k, ?_⟩
    intro e he f
    constructor
    · rintro ⟨he', _, _⟩
      exact he he'
    · rintro ⟨_, he', _⟩
      exact he he'
  · intro i k hik
    have he := congrArg (fun z : Rich d => z.1.archive.events.card) hik
    rw [hcard i, hcard k] at he
    exact Nat.add_left_cancel he
  · intro i k hik ⟨iso⟩
    have he : (y i).1.archive.events.card = (y k).1.archive.events.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr iso.eventEquiv
    rw [hcard i, hcard k] at he
    exact hik (Nat.add_left_cancel he)

end D5.S3.ConceptDynamics.Spacetime.InactiveArchiveFibers
