/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/CoordinateHalves/BinaryCubeSplitReconstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSharpSplit]
   utility: none
   digest: At sharp split weight the four sections reconstruct two shells at distance two. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSharpSplit
import D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubePartialShell

/-! The equality case of the opposite-section budget reconstructs both
partitions of the two six-cube neighborhoods, including their centers. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSplitReconstruction

open Finset
open scoped BigOperators
open BalancedCriticalSpectrum (Q)
local notation "flip" => BalancedCriticalSpectrum.flip
open BalancedCubeComponentBoundary (flip_injective)
open D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.BinaryCubeHalfKernel (adjacency adjacency_two_sections_eq)
open BinaryCubeKernelSupport (binarySites)
open BinaryCubeSharpSplit (twoSection sharp_split)
open BinaryCubePartialShell (partial_shell_image_card)
open BinaryCubePartialShell (shellWord)

/-- The open neighbourhood of a Boolean cube vertex. -/
abbrev neighborhood {n : ℕ} (p : Q n) : Finset (Q n) :=
  univ.image (flip p)

private theorem neighborhood_card {n : ℕ} (p : Q n) : (neighborhood p).card = n := by
  rw [card_image_of_injective _ (flip_injective p), card_univ, Fintype.card_fin]

private theorem neighborhood_injective : Function.Injective (@neighborhood 6) := by
  intro p q h
  by_contra hpq
  have hk : ∃ k, p k ≠ q k := by
    by_contra! hn
    exact hpq (funext hn)
  obtain ⟨k, hk⟩ := hk
  have hflip (i : Fin 6) (hi : i ≠ k) : flip p i = flip q k := by
    have hm : flip p i ∈ neighborhood q := h ▸ mem_image.mpr ⟨i, mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := mem_image.mp hm
    have hjk : j = k := by
      by_contra hne
      have he := congrFun hj k
      apply hk
      simpa [BalancedCriticalSpectrum.flip, Function.update_of_ne,
        hi.symm, (Ne.symm hne)] using he.symm
    simpa only [hjk] using hj.symm
  have hbound : ((univ : Finset (Fin 6)).erase k).card ≤ 1 := by
    apply card_le_one.mpr
    intro i hi j hj
    exact flip_injective p ((hflip i (mem_erase.mp hi).1).trans
      (hflip j (mem_erase.mp hj).1).symm)
  rw [card_erase_of_mem (mem_univ k), card_univ, Fintype.card_fin] at hbound
  omega

private theorem sites_add_of_disjoint {n : ℕ} (a d : Q n → ZMod 2)
    (h : Disjoint (binarySites a) (binarySites d)) :
    binarySites (a + d) = binarySites a ∪ binarySites d := by
  ext x
  simp only [binarySites, mem_filter, mem_univ, true_and, Pi.add_apply, mem_union]
  by_cases ha : a x = 0
  · simp [ha]
  · have hd : d x = 0 := by
      by_contra hd
      exact disjoint_left.mp h (mem_filter.mpr ⟨mem_univ _, ha⟩)
        (mem_filter.mpr ⟨mem_univ _, hd⟩)
    simp [hd]

private theorem partial_card_one_or_five (a : Q 6 → ZMod 2) (p q : Q 6)
    (ha : binarySites a ⊆ neighborhood p)
    (himg : binarySites (adjacency a) = neighborhood q) :
    (binarySites a).card = 1 ∨ (binarySites a).card = 5 := by
  let S : Finset (Fin 6) := univ.filter fun i => flip p i ∈ binarySites a
  have hS : S.image (flip p) = binarySites a := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      exact (mem_filter.mp hi).2
    · intro hx
      obtain ⟨i, _, rfl⟩ := mem_image.mp (ha hx)
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hx⟩, rfl⟩
  have hword : a = shellWord p S := by
    funext x
    unfold shellWord
    rw [hS]
    have hb : x ∈ binarySites a ↔ a x ≠ 0 := by simp [binarySites]
    by_cases h : a x = 0
    · simp [h, hb]
    · simp [hb, (show ∀ v : ZMod 2, v ≠ 0 → v = 1 from by decide) _ h]
  have hcard := partial_shell_image_card p S
  rw [← hword, himg, neighborhood_card] at hcard
  have hsc : S.card = (binarySites a).card := by
    rw [← hS, card_image_of_injective _ (flip_injective p)]
  have hle := card_le_card ha
  rw [neighborhood_card] at hle
  rw [hsc] at hcard
  generalize hr : (binarySites a).card = r at hcard hle ⊢
  interval_cases r <;> norm_num at *

/-- The singleton word at a vertex. -/
def delta {n : ℕ} (p : Q n) (x : Q n) : ZMod 2 :=
  if x = p then 1 else 0

private theorem eq_delta_of_sites_singleton {n : ℕ} (a : Q n → ZMod 2) (p : Q n)
    (h : binarySites a = {p}) : a = delta p := by
  funext x
  have hx : a x ≠ 0 ↔ x = p := by
    simpa [binarySites] using (show x ∈ binarySites a ↔ x ∈ ({p} : Finset (Q n)) by rw [h])
  unfold delta
  by_cases he : x = p
  · rw [ite_eq_left he]
    exact (show ∀ t : ZMod 2, t ≠ 0 → t = 1 from by decide) _ (hx.mpr he)
  · rw [ite_eq_right he]
    exact not_ne_iff.mp (fun hn => he (hx.mp hn))

/-- Applying adjacency to a point indicator gives its open shell indicator. -/
theorem adjacency_delta {n : ℕ} (p : Q n) (x : Q n) :
    adjacency (delta p) x = if x ∈ neighborhood p then 1 else 0 := by
  classical
  unfold adjacency
  by_cases hx : x ∈ neighborhood p
  · obtain ⟨j, _, hj⟩ := mem_image.mp hx
    have hp : flip x j = p := by rw [← hj, BalancedCriticalSpectrum.flip_flip]
    rw [ite_eq_left hx, sum_eq_single j]
    · simp [delta, hp]
    · intro i _ hi
      have hn : flip x i ≠ p := by
        intro he
        exact hi (flip_injective x (he.trans hp.symm))
      simp [delta, hn]
    · simp
  · rw [ite_eq_right hx]
    apply sum_eq_zero
    intro i _
    have hn : flip x i ≠ p := by
      intro he
      apply hx
      exact mem_image.mpr ⟨i, mem_univ _, by rw [← he, BalancedCriticalSpectrum.flip_flip]⟩
    simp [delta, hn]

private theorem sites_adjacency_delta {n : ℕ} (p : Q n) :
    binarySites (adjacency (delta p)) = neighborhood p := by
  ext x
  simp only [binarySites, mem_filter, mem_univ, true_and, adjacency_delta]
  by_cases hx : x ∈ neighborhood p <;> simp [hx]

private theorem singleton_identification (a : Q 6 → ZMod 2) (q : Q 6)
    (hcard : (binarySites a).card = 1)
    (himg : binarySites (adjacency a) = neighborhood q) :
    binarySites a = {q} := by
  obtain ⟨r, hr⟩ := card_eq_one.mp hcard
  have hword := eq_delta_of_sites_singleton a r hr
  rw [hword, sites_adjacency_delta] at himg
  rw [hr, neighborhood_injective himg]

private theorem complement_of_partition {n : ℕ} {A D : Finset (Q n)} {p q : Q n}
    (hunion : A ∪ D = neighborhood p) (hdis : Disjoint A D) (ha : A = {q}) :
    D = (neighborhood p).erase q := by
  ext x
  rw [mem_erase, ← hunion, mem_union, ha, mem_singleton]
  constructor
  · intro hd
    have hn : x ≠ q := by
      intro he
      exact disjoint_left.mp hdis (by rw [ha, mem_singleton]; exact he) hd
    exact ⟨hn, Or.inr hd⟩
  · rintro ⟨hn, he | hd⟩
    · exact (hn he).elim
    · exact hd

private theorem pair_reconstruction (a d : Q 6 → ZMod 2) (p q : Q 6)
    (hu : binarySites (a + d) = neighborhood p)
    (hdis : Disjoint (binarySites a) (binarySites d))
    (ha : binarySites (adjacency a) = neighborhood q)
    (hd : binarySites (adjacency d) = neighborhood q) :
    q ∈ neighborhood p ∧
    ((binarySites a = {q} ∧ binarySites d = (neighborhood p).erase q) ∨
     (binarySites d = {q} ∧ binarySites a = (neighborhood p).erase q)) := by
  have hunion := (sites_add_of_disjoint a d hdis).symm.trans hu
  have hsuba : binarySites a ⊆ neighborhood p := by rw [← hunion]; exact subset_union_left
  have hsubd : binarySites d ⊆ neighborhood p := by rw [← hunion]; exact subset_union_right
  rcases partial_card_one_or_five a p q hsuba ha with hcard | hcard
  · have hs := singleton_identification a q hcard ha
    exact ⟨hsuba (by rw [hs]; simp), Or.inl ⟨hs, complement_of_partition hunion hdis hs⟩⟩
  · have hsum := card_union_of_disjoint hdis
    rw [hunion, neighborhood_card, hcard] at hsum
    have hs := singleton_identification d q (by omega) hd
    rw [union_comm] at hunion
    exact ⟨hsubd (by rw [hs]; simp), Or.inr ⟨hs, complement_of_partition hunion hdis.symm hs⟩⟩

/-- A sharp fixed-coordinate split has two adjacent Q6 centers. Each
opposite pair consists of the other center and its shell complement. -/
theorem sharp_split_reconstruction (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hw : (binarySites f).card ≤ 12)
    (hu : twoSection f false false + twoSection f true true ≠ 0)
    (hv : twoSection f true false + twoSection f false true ≠ 0) :
    (binarySites f).card = 12 ∧ ∃ p q : Q 6, q ∈ neighborhood p ∧ p ∈ neighborhood q ∧
    ((binarySites (twoSection f false false) = {q} ∧
      binarySites (twoSection f true true) = (neighborhood p).erase q) ∨
     (binarySites (twoSection f true true) = {q} ∧
      binarySites (twoSection f false false) = (neighborhood p).erase q)) ∧
    ((binarySites (twoSection f true false) = {p} ∧
      binarySites (twoSection f false true) = (neighborhood q).erase p) ∨
     (binarySites (twoSection f false true) = {p} ∧
      binarySites (twoSection f true false) = (neighborhood q).erase p)) := by
  obtain ⟨hweight, ⟨p, hp⟩, ⟨q, hq⟩, hdis₁, hdis₂⟩ := sharp_split f hf hw hu hv
  have ha : adjacency (twoSection f false false) =
      twoSection f true false + twoSection f false true := adjacency_two_sections_eq hf false false
  have hd : adjacency (twoSection f true true) =
      twoSection f true false + twoSection f false true := by
    exact (adjacency_two_sections_eq hf true true).trans (add_comm _ _)
  have hb : adjacency (twoSection f true false) =
      twoSection f false false + twoSection f true true := adjacency_two_sections_eq hf true false
  have hc : adjacency (twoSection f false true) =
      twoSection f false false + twoSection f true true := by
    exact (adjacency_two_sections_eq hf false true).trans (add_comm _ _)
  obtain ⟨hpq, hpart₁⟩ := pair_reconstruction _ _ p q hp hdis₁
    (by rw [ha, hq]) (by rw [hd, hq])
  obtain ⟨hqp, hpart₂⟩ := pair_reconstruction _ _ q p hq hdis₂
    (by rw [hb, hp]) (by rw [hc, hp])
  exact ⟨hweight, p, q, hpq, hqp, hpart₁, hpart₂⟩

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSplitReconstruction.sharp_split_reconstruction' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sharp_split_reconstruction

private theorem eq_shell_complement_word (a : Q 6 → ZMod 2) (p q : Q 6)
    (hq : q ∈ neighborhood p) (hs : binarySites a = (neighborhood p).erase q) :
    a = adjacency (delta p) + delta q := by
  funext x
  have hm : a x ≠ 0 ↔ x ≠ q ∧ x ∈ neighborhood p := by
    simpa [binarySites, mem_erase] using
      (show x ∈ binarySites a ↔ x ∈ (neighborhood p).erase q by rw [hs])
  simp only [Pi.add_apply, adjacency_delta, delta]
  by_cases he : x = q
  · subst x
    have hz : a q = 0 := by
      by_contra hn
      exact (hm.mp hn).1 rfl
    simp [hz, hq, ZModModule.add_self]
  · by_cases hx : x ∈ neighborhood p
    · have ha := (show ∀ t : ZMod 2, t ≠ 0 → t = 1 from by decide) _
        (hm.mpr ⟨he, hx⟩)
      simp [he, hx, ha]
    · have ha : a x = 0 := by
        by_contra hn
        exact hx (hm.mp hn).2
      simp [he, hx, ha]

private theorem twoSection_adjacency {n : ℕ} (f : Q (n + 2) → ZMod 2) (a b : Bool) :
    twoSection (adjacency f) a b =
      twoSection f (!a) b + twoSection f a (!b) + adjacency (twoSection f a b) := by
  funext x
  simp only [twoSection, adjacency, Pi.add_apply]
  rw [Fin.sum_univ_succ]
  simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
    Fin.cons_succ, ← Fin.cons_update]
  rw [Fin.sum_univ_succ]
  simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
    Fin.cons_succ, ← Fin.cons_update, add_assoc]

private theorem twoSection_add {n : ℕ} (f g : Q (n + 2) → ZMod 2) (a b : Bool) :
    twoSection (f + g) a b = twoSection f a b + twoSection g a b := rfl

private theorem twoSection_delta {n : ℕ} (a b s t : Bool) (p : Q n) :
    twoSection (delta (Fin.cons s (Fin.cons t p))) a b =
      if a = s ∧ b = t then delta p else 0 := by
  funext x
  by_cases h : a = s ∧ b = t
  · obtain ⟨rfl, rfl⟩ := h
    simp [twoSection, delta, Fin.cons_inj]
  · simp [twoSection, delta, Fin.cons_inj, h]
    exact fun ha hb _ => h ⟨ha, hb⟩

private theorem eq_of_twoSections_eq {n : ℕ} {f g : Q (n + 2) → ZMod 2}
    (h : ∀ a b, twoSection f a b = twoSection g a b) : f = g := by
  funext z
  have he := congrFun (h (z 0) (Fin.tail z 0)) (Fin.tail (Fin.tail z))
  simpa only [twoSection, Fin.cons_self_tail] using he

private theorem assemble_shells (f : Q 8 → ZMod 2) (p q : Q 6) (s t : Bool)
    (he : twoSection f s s = delta q)
    (he' : twoSection f (!s) (!s) = adjacency (delta p) + delta q)
    (ho : twoSection f t (!t) = delta p)
    (ho' : twoSection f (!t) t = adjacency (delta q) + delta p) :
    f = adjacency (delta (Fin.cons (!t) (Fin.cons t q)) +
      delta (Fin.cons (!s) (Fin.cons (!s) p))) := by
  apply eq_of_twoSections_eq
  intro a b
  have hadd (g h : Q 8 → ZMod 2) : adjacency (g + h) = adjacency g + adjacency h := by
    funext x
    simp only [adjacency, Pi.add_apply, sum_add_distrib]
  simp only [hadd, twoSection_adjacency, twoSection_add, twoSection_delta]
  have hz : adjacency (0 : Q 6 → ZMod 2) = 0 := by
    funext x
    simp [adjacency]
  cases s <;> cases t <;> cases a <;> cases b <;>
    simp_all [hz, add_comm]

/-- For a sharp split, the entire Q8 word is the sum of the two open
neighborhood indicators, with centers separated by exactly two flips. -/
theorem sharp_split_two_shells (f : Q 8 → ZMod 2) (hf : adjacency f = 0)
    (hw : (binarySites f).card ≤ 12)
    (hu : twoSection f false false + twoSection f true true ≠ 0)
    (hv : twoSection f true false + twoSection f false true ≠ 0) :
    (binarySites f).card = 12 ∧
    ∃ x y : Q 8, (∃ i j : Fin 8, i ≠ j ∧ y = flip (flip x i) j) ∧
      f = adjacency (delta x + delta y) := by
  obtain ⟨hw', p, q, hpq, hqp, he, ho⟩ := sharp_split_reconstruction f hf hw hu hv
  have he' : ∃ s : Bool, twoSection f s s = delta q ∧
      twoSection f (!s) (!s) = adjacency (delta p) + delta q := by
    rcases he with ⟨ha, hd⟩ | ⟨hd, ha⟩
    · exact ⟨false, eq_delta_of_sites_singleton _ _ ha,
        eq_shell_complement_word _ _ _ hpq hd⟩
    · exact ⟨true, eq_delta_of_sites_singleton _ _ hd,
        eq_shell_complement_word _ _ _ hpq ha⟩
  have ho' : ∃ t : Bool, twoSection f t (!t) = delta p ∧
      twoSection f (!t) t = adjacency (delta q) + delta p := by
    rcases ho with ⟨hb, hc⟩ | ⟨hc, hb⟩
    · exact ⟨true, eq_delta_of_sites_singleton _ _ hb,
        eq_shell_complement_word _ _ _ hqp hc⟩
    · exact ⟨false, eq_delta_of_sites_singleton _ _ hc,
        eq_shell_complement_word _ _ _ hqp hb⟩
  obtain ⟨s, hs, hs'⟩ := he'
  obtain ⟨t, ht, ht'⟩ := ho'
  obtain ⟨k, _, hk⟩ := mem_image.mp hqp
  simp only [BalancedCriticalSpectrum.flip] at hk
  refine ⟨hw', _, _, ?_, assemble_shells f p q s t hs hs' ht ht'⟩
  cases s <;> cases t
  · refine ⟨(0 : Fin 7).succ, k.succ.succ, by
      intro h
      have hv := congrArg Fin.val h
      simp at hv, ?_⟩
    simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_succ, ← Fin.cons_update, Bool.not_false, hk]
  · refine ⟨0, k.succ.succ, by
      intro h
      have hv := congrArg Fin.val h
      simp at hv, ?_⟩
    simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_succ, ← Fin.cons_update, Bool.not_false, Bool.not_true, hk]
  · refine ⟨0, k.succ.succ, by
      intro h
      have hv := congrArg Fin.val h
      simp at hv, ?_⟩
    simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_succ, ← Fin.cons_update, Bool.not_false, Bool.not_true, hk]
  · refine ⟨(0 : Fin 7).succ, k.succ.succ, by
      intro h
      have hv := congrArg Fin.val h
      simp at hv, ?_⟩
    simp only [BalancedCriticalSpectrum.flip, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_succ, ← Fin.cons_update, Bool.not_true, hk]

/--
info: 'D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSplitReconstruction.sharp_split_two_shells' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms sharp_split_two_shells

end D5.S3.Combinatorics.Graph.HypercubeCritical.CoordinateHalves.BinaryCubeSplitReconstruction
