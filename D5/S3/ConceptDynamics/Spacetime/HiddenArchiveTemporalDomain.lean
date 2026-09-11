/- GID: D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.CurrentSpatialProjectionPreservesTemporalDomains; result=D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.current_spatial_projection_domain_refutation; claim=D5/S3/ConceptDynamics/Spacetime/HiddenArchiveTemporalDomain.CurrentSpatialProjectionPreservesTemporalDomains
   digest: One inactive archived event preserves literal current data and double spatial charge but destroys a temporal domain. -/

import D5.S3.ConceptDynamics.Spacetime.IntegerRepresentatives
import D5.S3.ConceptDynamics.Spacetime.TemporalComposition
import Mathlib.Algebra.BigOperators.Finsupp.Basic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.ConceptDynamics.Spacetime.HiddenArchiveTemporalDomain

open D5.S0.History.Spacetime.HFEncoding
open D5.S0.History.Spacetime.ArchiveCarrier
open ComplementCharge IntegerRepresentatives TemporalComposition
open scoped BigOperators

noncomputable section
local instance : DecidableEq HF := Classical.decEq _

/-- The literal finite-support sum of signed point masses on a set of occurrences. -/
def spatialCharge {d : Nat} (c : Context d) (s : Finset c.Event) :
    (Fin d → Int) →₀ Int :=
  ∑ e ∈ s, Finsupp.single (c.archive.attributes e).position (contribution c e)

/-- Both the entire current region and the selected subset are observed. -/
def pi {d : Nat} (x : Rich d) : ((Fin d → Int) →₀ Int) × ((Fin d → Int) →₀ Int) :=
  (spatialCharge x.1 x.1.current, spatialCharge x.1 x.2.val)

private def oldAttributes : Attributes 3 :=
  { time := 2, position := 0, positive := true, source := FreeMagma.of 9 }

private theorem fresh : eventName 1 true ∉ U.1.archive.events := by
  intro h
  change eventName 1 true ∈ eventNames 1 at h
  unfold eventNames at h
  obtain ⟨⟨i, b⟩, _, hi⟩ := Finset.mem_image.mp h
  have he : (i.val, b) = (1, true) := eventName_injective hi
  have : i.val = 1 := congrArg Prod.fst he
  have : i.val < 1 := i.isLt
  omega

private def oldArchive : Archive 3 where
  events := insert (eventName 1 true) U.1.archive.events
  attributes e := if h : e.val ∈ U.1.archive.events then U.1.archive.attributes ⟨e.val, h⟩
    else oldAttributes
  causal _ _ := False
  irrefl _ h := h
  trans _ _ _ h _ := h
  time_lt _ _ h := h.elim

/-- The map changes only the subtype membership proof, never the HF occurrence name. -/
private def oldEmbedding : ArchiveEmbedding U.1.archive oldArchive where
  eventMap :=
    { toFun e := ⟨e.val, Finset.mem_insert_of_mem e.property⟩
      inj' := by
        intro x y h
        apply Subtype.ext
        exact congrArg (fun z : oldArchive.Event => z.val) h }
  attributes_eq e := by
    change (if h : e.val ∈ U.1.archive.events then U.1.archive.attributes ⟨e.val, h⟩
      else oldAttributes) = _
    rw [dif_pos e.property]
  causal_iff _ _ := Iff.rfl

private def oldContext : Context 3 :=
  ⟨oldArchive, U.1.current.map oldEmbedding.eventMap⟩

/-- Exactly one fresh archived occurrence is added; current and selected names are copied. -/
def U_old : Rich 3 :=
  ⟨oldContext, ⟨U.2.val.map oldEmbedding.eventMap, Finset.map_subset_map.mpr U.2.property⟩⟩

private def added : U_old.1.archive.Event :=
  ⟨eventName 1 true, Finset.mem_insert_self _ _⟩

private theorem added_attributes : U_old.1.archive.attributes added = oldAttributes := by
  simp only [U_old, oldContext, oldArchive, added, dif_neg fresh]

private theorem added_not_current : added ∉ U_old.1.current := by
  intro h
  obtain ⟨e, _, he⟩ := Finset.mem_map.mp h
  have hv : e.val = eventName 1 true := congrArg Subtype.val he
  exact fresh (hv ▸ e.property)

private theorem added_not_selected : added ∉ U_old.2.val :=
  fun h => added_not_current (U_old.2.property h)

private theorem charge_old (s : Finset U.1.Event) :
    charge U_old.1 (s.map oldEmbedding.eventMap) = charge U.1 s := by
  unfold charge
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun a : Attributes 3 => if a.positive then (1 : Int) else -1)
    (oldEmbedding.attributes_eq e)

private theorem spatial_old (s : Finset U.1.Event) :
    spatialCharge U_old.1 (s.map oldEmbedding.eventMap) = spatialCharge U.1 s := by
  unfold spatialCharge
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  exact congrArg (fun a : Attributes 3 =>
    Finsupp.single a.position (if a.positive then (1 : Int) else -1))
    (oldEmbedding.attributes_eq e)

private theorem pi_old : pi U_old = pi U :=
  Prod.ext (spatial_old U.1.current) (spatial_old U.2.val)

private theorem spatial_at_zero {d : Nat} (c : Context d) (s : Finset c.Event)
    (h : ∀ e ∈ s, (c.archive.attributes e).position = 0) :
    spatialCharge c s = Finsupp.single 0 (charge c s) := by
  unfold spatialCharge charge
  calc
    (∑ e ∈ s, Finsupp.single (c.archive.attributes e).position (contribution c e)) =
        ∑ e ∈ s, Finsupp.single 0 (contribution c e) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [h e he]
    _ = _ := (map_sum (Finsupp.singleAddHom 0) _ s).symm

private theorem unit_pi : pi U = (0, Finsupp.single 0 1) := by
  have hz (e : U.1.Event) : (U.1.archive.attributes e).position = 0 := rfl
  have hb := representative_balanced 3 1
  have hq := representative_readout 3 1
  change background U.1 = 0 at hb
  change q U = 1 at hq
  unfold pi
  rw [spatial_at_zero _ _ (fun e _ => hz e), spatial_at_zero _ _ (fun e _ => hz e)]
  change (Finsupp.single 0 (background U.1), Finsupp.single 0 (q U)) = _
  rw [hb, hq, Finsupp.single_zero]

private theorem unit_guard : Guard U.1.archive (shiftRich U 1).1.archive := by
  intro e f
  change (0 : Int) < 0 + 1
  decide

private def rightEvent : (shiftRich U 1).1.archive.Event :=
  ⟨eventName 0 true, eventNames_mem 1 ⟨0, by decide⟩ true⟩

private theorem separating_times :
    (U_old.1.archive.attributes added).time = 2 ∧
      ((shiftRich U 1).1.archive.attributes rightEvent).time = 1 := by
  constructor
  · rw [added_attributes]; rfl
  · rfl

private theorem old_not_guard : ¬ Guard U_old.1.archive (shiftRich U 1).1.archive := by
  intro h
  have hlt := h added rightEvent
  rw [separating_times.1, separating_times.2] at hlt
  omega

/-- Equality of current spatial projections preserves every right temporal domain
on balanced rich representations in dimension three. -/
def CurrentSpatialProjectionPreservesTemporalDomains : Prop :=
  ∀ x x' y : Rich 3, Balanced x.1 → Balanced x'.1 → Balanced y.1 →
    pi x = pi x' → (Guard x.1.archive y.1.archive ↔ Guard x'.1.archive y.1.archive)

/-- The complete inactive-event witness includes literal names, all attributes,
both point-mass sums, the legal output, and the explicit obstructing event pair. -/
theorem hidden_archive_preserves_current_changes_temporal_domain :
    let Y := shiftRich U 1
    ∃ j : ArchiveEmbedding U.1.archive U_old.1.archive,
    ∃ e : U_old.1.archive.Event, ∃ f : Y.1.archive.Event,
      (∀ a, (j.eventMap a).val = a.val) ∧
      e.val = eventName 1 true ∧ e.val ∉ U.1.archive.events ∧
      U_old.1.archive.events = insert e.val U.1.archive.events ∧
      U_old.1.current = U.1.current.map j.eventMap ∧
      U_old.2.val = U.2.val.map j.eventMap ∧
      U_old.1.current.image Subtype.val = U.1.current.image Subtype.val ∧
      U_old.2.val.image Subtype.val = U.2.val.image Subtype.val ∧
      (∀ a ∈ U.1.current, U_old.1.archive.attributes (j.eventMap a) =
        U.1.archive.attributes a) ∧
      U_old.1.archive.attributes e =
        { time := 2, position := 0, positive := true, source := FreeMagma.of 9 } ∧
      (∀ a b, ¬ U_old.1.archive.causal a b) ∧
      e ∉ U_old.1.current ∧ e ∉ U_old.2.val ∧
      Balanced U.1 ∧ Balanced U_old.1 ∧ Balanced Y.1 ∧
      pi U = (0, Finsupp.single 0 1) ∧ pi U_old = (0, Finsupp.single 0 1) ∧
      (U_old.1.archive.attributes e).time = 2 ∧ (Y.1.archive.attributes f).time = 1 ∧
      (∃ h : Guard U.1.archive Y.1.archive, q (temporal U Y h) = 2) ∧
      ¬ Guard U_old.1.archive Y.1.archive := by
  dsimp only
  refine ⟨oldEmbedding, added, rightEvent, fun _ => rfl, rfl, fresh, rfl, rfl, rfl,
    ?_, ?_, fun a _ => oldEmbedding.attributes_eq a, added_attributes,
    fun _ _ h => h, added_not_current, added_not_selected,
    representative_balanced 3 1, ?_, ?_, unit_pi, pi_old.trans unit_pi,
    separating_times.1, separating_times.2, ⟨unit_guard, ?_⟩, old_not_guard⟩
  · simp only [U_old, oldContext, Finset.map_eq_image, Finset.image_image]
    rfl
  · simp only [U_old, Finset.map_eq_image, Finset.image_image]
    rfl
  · change charge U_old.1 (U.1.current.map oldEmbedding.eventMap) = 0
    rw [charge_old]
    exact representative_balanced 3 1
  · exact representative_balanced 3 1
  · rw [q_temporal, q_shift]
    change q (representative 3 1) + q (representative 3 1) = 2
    rw [representative_readout]
    rfl

/-- The preserved double spatial readout cannot determine full-archive legality. -/
theorem current_spatial_projection_domain_refutation :
    ¬ CurrentSpatialProjectionPreservesTemporalDomains := by
  intro h
  obtain ⟨j, e, f, _, _, _, _, _, _, _, _, _, _, _, _, _, hu, ho, hy,
    hp, hp', _, _, ⟨hg, _⟩, hn⟩ :=
      hidden_archive_preserves_current_changes_temporal_domain
  exact hn ((h U U_old (shiftRich U 1) hu ho hy (hp.trans hp'.symm)).mp hg)

end
end D5.S3.ConceptDynamics.Spacetime.HiddenArchiveTemporalDomain
