/- GID: D5/S3/Topology/StableCategory/HalesJewettCategoricalCover
   generality: G
   mirror-B: D5/B/S3/Topology/StableCategory/HalesJewettCategoricalCover
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Aligned chains force unbounded categorical covers after one subdivision. -/

import Mathlib.Combinatorics.HalesJewett
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Order.Fin.Basic
import Mathlib.Order.NonemptyFiniteChains
import Mathlib.Tactic.FinCases
import D5.S3.Topology.ConnectedCategoryGraft

/-!
# The Hales–Jewett obstruction to categorical lower covers at depth one

A word of full chains gives a chain in the power by aligning the ranks.
Colour that chain by a categorical lower set containing it. A monochromatic
line places the image of the entire subdivided factor in one lower set.
Projection at a variable coordinate retracts that image onto the subdivided
factor, so the inclusion fence of the lower set gives a contraction fence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace D5.S3.Topology.StableCategory.HalesJewettCategoricalCover

open ConnectedCategoryGraft (Categorical HasCategoricalCover)
open PartialOrder (NonemptyFiniteChains)
open PartialOrder.NonemptyFiniteChains (orderHomMap)
open Relation (EqvGen)

private theorem mapFence {S T : Type*} [Preorder S] [Preorder T] {f : S → T}
    (hf : Monotone f) {a b : S} (hab : EqvGen (· ≤ ·) a b) :
    EqvGen (· ≤ ·) (f a) (f b) := by
  induction hab with
  | rel _ _ h => exact .rel _ _ (hf h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ ih₁ ih₂ => exact .trans _ _ _ ih₁ ih₂

private theorem fenceOfCategoricalSplit {S T : Type*} [PartialOrder S] [PartialOrder T]
    {U : Set T} (embed : S →o U) (project : T →o S)
    (hsplit : ∀ s, project (embed s).val = s) (hU : Categorical U) :
    ∃ c : S, EqvGen (· ≤ ·) (OrderHom.id : S →o S) (OrderHom.const S c) := by
  obtain ⟨c, hc⟩ := hU
  let pull (f : U →o T) : S →o S := project.comp (f.comp embed)
  have hpull : Monotone pull := fun _ _ h s =>
    project.monotone (OrderHom.le_def.mp h (embed s))
  have hstart : pull (OrderEmbedding.subtype U).toOrderHom = OrderHom.id := by
    apply OrderHom.ext
    exact funext hsplit
  have hend : pull (OrderHom.const U c) = OrderHom.const S (project c) := rfl
  exact ⟨project c, by simpa only [hstart, hend] using mapFence hpull hc⟩

/-- A one-piece categorical lower cover is equivalent to an identity fence to a constant. -/
theorem hasCategoricalCover_one_iff {S : Type*} [PartialOrder S] :
    HasCategoricalCover S 1 ↔
      ∃ c : S, EqvGen (· ≤ ·) (OrderHom.id : S →o S) (OrderHom.const S c) := by
  constructor
  · rintro ⟨U, hU, hcover⟩
    have hmem (s : S) : s ∈ U 0 := by
      obtain ⟨i, hi⟩ := hcover s
      have hi₀ : i = 0 := Subsingleton.elim _ _
      simpa only [hi₀] using hi
    let embed : S →o U 0 := ⟨fun s => ⟨s, hmem s⟩, fun _ _ h => h⟩
    exact fenceOfCategoricalSplit embed (OrderHom.id : S →o S) (fun _ => rfl) (hU 0).2
  · rintro ⟨c, hc⟩
    refine ⟨fun _ => Set.univ, ?_, fun s => ⟨0, Set.mem_univ s⟩⟩
    intro _
    refine ⟨by intro a b _ _; exact Set.mem_univ a, c, ?_⟩
    let inc := (OrderEmbedding.subtype (Set.univ : Set S)).toOrderHom
    let restrict (f : S →o S) : (Set.univ : Set S) →o S := f.comp inc
    have hrestrict : Monotone restrict := fun _ _ h s => OrderHom.le_def.mp h (inc s)
    exact mapFence hrestrict hc

private def synchronizedChain {X A : Type*} [PartialOrder X] {h n : ℕ}
    (r₀ : Fin h) (letter : A → Fin h ↪o X) (word : Fin n → A) :
    NonemptyFiniteChains (Fin n → X) :=
  (⟨Finset.univ, ⟨r₀, Finset.mem_univ _⟩, fun a b => le_total a.val b.val⟩ :
    NonemptyFiniteChains (Fin h)).map
      ⟨fun r i => letter (word i) r, fun _ _ hrs i => (letter (word i)).monotone hrs⟩

/-- A finite alphabet of full chains gives unbounded categorical lower-cover
size after one subdivision of the powers. The rank is monotone and each
letter is an order embedding which is a section of the rank. Every nonempty
chain is contained in the range of a letter, so the finitely many letters
also cover the underlying poset. -/
theorem exists_no_categorical_cover {X A : Type*} [PartialOrder X] [Finite A] {h : ℕ}
    (rank : X →o Fin h) (letter : A → Fin h ↪o X)
    (rank_letter : ∀ a r, rank (letter a r) = r)
    (extend : ∀ s : NonemptyFiniteChains X, ∃ a, ∀ x ∈ s.finset, x ∈ Set.range (letter a))
    (noOne : ¬ HasCategoricalCover (NonemptyFiniteChains X) 1) (k : ℕ) :
    ∃ n : ℕ, ¬ HasCategoricalCover (NonemptyFiniteChains (Fin n → X)) k := by
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    obtain ⟨ι, inst, hj⟩ := Combinatorics.Line.exists_mono_in_high_dimension A (Fin k)
    let : Fintype ι := inst
    let index := Fintype.equivFin ι
    refine ⟨Fintype.card ι, ?_⟩
    rintro ⟨U, hU, hcover⟩
    let sync := synchronizedChain (n := Fintype.card ι) (rank x₀) letter
    let color (w : Fin (Fintype.card ι) → A) : Fin k := Classical.choose (hcover (sync w))
    have hcolor (w : Fin (Fintype.card ι) → A) : sync w ∈ U (color w) :=
      Classical.choose_spec (hcover (sync w))
    obtain ⟨line, c, hmono⟩ := hj (fun w => color (w ∘ index.symm))
    obtain ⟨j, hjvar⟩ := line.proper
    let embed : X →o (Fin (Fintype.card ι) → X) := {
      toFun x i := (line.idxFun (index.symm i)).elim x (fun a => letter a (rank x))
      monotone' := by
        intro x y hxy i
        change (line.idxFun (index.symm i)).elim x (fun a => letter a (rank x)) ≤
          (line.idxFun (index.symm i)).elim y (fun a => letter a (rank y))
        cases line.idxFun (index.symm i) with
        | none => exact hxy
        | some a => exact (letter a).monotone (rank.monotone hxy) }
    let project : (Fin (Fintype.card ι) → X) →o X :=
      ⟨fun v => v (index j), fun _ _ hv => hv (index j)⟩
    have hproject (x : X) : project (embed x) = x := by
      change (line.idxFun (index.symm (index j))).elim x (fun a => letter a (rank x)) = x
      rw [index.symm_apply_apply, hjvar]
      rfl
    have hmem (s : NonemptyFiniteChains X) : orderHomMap embed s ∈ U c := by
      obtain ⟨a, ha⟩ := extend s
      have hword : sync (line a ∘ index.symm) ∈ U c := by
        have h := hcolor (line a ∘ index.symm)
        rw [show color (line a ∘ index.symm) = c from hmono a] at h
        exact h
      refine (hU c).1 ?_ hword
      change (s.map embed).finset ⊆ (sync (line a ∘ index.symm)).finset
      intro y hy
      obtain ⟨x, hx, rfl⟩ := (NonemptyFiniteChains.mem_map_iff s embed y).mp hy
      obtain ⟨r, hr⟩ := ha x hx
      have hrank : r = rank x :=
        (rank_letter a r).symm.trans (congrArg (fun z : X => rank z) hr)
      have halign : letter a (rank x) = x := by simpa only [hrank] using hr
      change embed x ∈ (synchronizedChain (rank x₀) letter (line a ∘ index.symm)).finset
      unfold synchronizedChain
      refine (NonemptyFiniteChains.mem_map_iff _ _ _).mpr ⟨rank x, Finset.mem_univ _, ?_⟩
      funext i
      change letter (line a (index.symm i)) (rank x) =
        (line.idxFun (index.symm i)).elim x (fun b => letter b (rank x))
      rw [Combinatorics.Line.coe_apply]
      cases line.idxFun (index.symm i) with
      | none => exact halign
      | some b => rfl
    let intoPiece : NonemptyFiniteChains X →o U c :=
      ⟨fun s => ⟨orderHomMap embed s, hmem s⟩, fun _ _ hst => (orderHomMap embed).monotone hst⟩
    have hsplit (s : NonemptyFiniteChains X) : orderHomMap project (intoPiece s).val = s := by
      apply NonemptyFiniteChains.ext
      apply Finset.ext
      intro x
      change x ∈ ((s.map embed).map project).finset ↔ x ∈ s.finset
      simp only [NonemptyFiniteChains.mem_map_iff]
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, hp⟩
        have heq : z = x := (hproject z).symm.trans hp
        exact heq ▸ hz
      · intro hx
        exact ⟨embed x, ⟨x, hx, rfl⟩, hproject x⟩
    exact noOne (hasCategoricalCover_one_iff.mpr
      (fenceOfCategoricalSplit intoPiece (orderHomMap project) hsplit (hU c).2))
  · cases k with
    | zero =>
      refine ⟨0, ?_⟩
      rintro ⟨_, _, hcover⟩
      let emptyWord : Fin 0 → X := fun i => Fin.elim0 i
      let s : NonemptyFiniteChains (Fin 0 → X) :=
        ⟨{emptyWord}, Finset.singleton_nonempty _, fun _ _ => Or.inl (fun i => Fin.elim0 i)⟩
      obtain ⟨i, _⟩ := hcover s
      exact Fin.elim0 i
    | succ k =>
      refine ⟨1, ?_⟩
      rintro ⟨U, hU, _⟩
      obtain ⟨s, _⟩ := (hU 0).2
      obtain ⟨w, _⟩ := s.nonempty
      exact hX ⟨w 0⟩

end D5.S3.Topology.StableCategory.HalesJewettCategoricalCover
