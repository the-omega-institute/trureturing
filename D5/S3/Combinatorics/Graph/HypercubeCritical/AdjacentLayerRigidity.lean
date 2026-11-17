/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/AdjacentLayerRigidity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting]
   utility: none
   digest: Actual adjacent-layer balanced cubic supports of size fifty-four in Q9 have Gray reconstruction. -/
import D5.S3.Combinatorics.Graph.HypercubeCritical.ThinSliceGrayReconstruction
import D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Batteries.Tactic.OpenPrivate
/-! Literal face incidences force a fifteen-vertex coordinate half. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace D5.S3.Combinatorics.Graph.HypercubeCritical.AdjacentLayerRigidity
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open D5.S3.Combinatorics.Graph.Hypercube
open BalancedCriticalSpectrum (Q flip IsBalanced)
open BalancedCubeLowerBound (coordinateSlice)
open private adjacent_exists_flip from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeGirth
open private directions directions_card regular_directions exterior_even from
  D5.S3.Combinatorics.Graph.HypercubeCritical.BalancedCubeComponentBoundary
private abbrev Coord := Fin 9
private abbrev Face := Finset Coord
private def occupied (x : Q 9) : Face := Finset.univ.filter fun i => x i = true
private def point (s : Face) : Q 9 := fun i => decide (i ∈ s)
@[simp] private theorem mem_occupied (x : Q 9) (i : Coord) :
    i ∈ occupied x ↔ x i = true := by simp [occupied]
@[simp] private theorem occupied_point (s : Face) : occupied (point s) = s := by
  ext i
  simp [point]
@[simp] private theorem point_occupied (x : Q 9) : point (occupied x) = x := by
  funext i
  cases hi : x i <;> simp [point, hi]
private theorem occupied_injective : Function.Injective occupied :=
  Function.LeftInverse.injective point_occupied
private theorem point_injective : Function.Injective point :=
  Function.LeftInverse.injective occupied_point
private def selected (C : Finset (Q 9)) : Finset Face := C.image occupied
@[simp] private theorem mem_selected (C : Finset (Q 9)) (s : Face) :
    s ∈ selected C ↔ point s ∈ C := by
  constructor
  · rintro h
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp h
    simpa using hx
  · intro h
    exact Finset.mem_image.mpr ⟨point s, h, occupied_point s⟩
private theorem card_selected (C : Finset (Q 9)) : (selected C).card = C.card :=
  Finset.card_image_of_injective C occupied_injective
private def layer (A : Finset Face) (r : Nat) := A.filter fun s => s.card = r
private theorem occupied_flip (x : Q 9) (i : Coord) :
    occupied (flip x i) = if i ∈ occupied x then (occupied x).erase i
      else insert i (occupied x) := by
  ext j
  by_cases hji : j = i
  · subst j
    cases hi : x i <;> simp [BalancedCriticalSpectrum.flip, hi]
  · by_cases hxi : x i = true
    · simp [occupied, BalancedCriticalSpectrum.flip, hji, hxi]
    · simp [occupied, BalancedCriticalSpectrum.flip, hji, hxi]
private theorem insert_adj (s : Face) (i : Coord) (hi : i ∉ s) :
    (hypercube 9).Adj (point s) (point (insert i s)) := by
  have he : point (insert i s) = flip (point s) i := by
    funext j
    by_cases hj : j = i
    · subst j; simp [point, BalancedCriticalSpectrum.flip, hi]
    · simp [point, BalancedCriticalSpectrum.flip, hj]
  rw [he]
  exact BalancedCriticalSpectrum.flip_adj _ _
private theorem subset_succ_adj {s t : Face} (hst : s ⊆ t)
    (hc : s.card + 1 = t.card) : (hypercube 9).Adj (point s) (point t) := by
  have hd : (t \ s).card = 1 := by rw [Finset.card_sdiff_of_subset hst]; omega
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hd
  have hni : i ∉ s := (Finset.mem_sdiff.mp (hi ▸ Finset.mem_singleton_self i)).2
  have he : t = insert i s := by
    have hu := Finset.sdiff_union_of_subset hst
    rw [hi, Finset.singleton_union] at hu
    exact hu.symm
  rw [he]
  exact insert_adj s i hni
private theorem adjacent_sets {s t : Face}
    (ha : (hypercube 9).Adj (point s) (point t)) :
    (s ⊆ t ∧ s.card + 1 = t.card) ∨ (t ⊆ s ∧ t.card + 1 = s.card) := by
  obtain ⟨i, hi⟩ := adjacent_exists_flip ha
  have he := congrArg occupied hi
  rw [occupied_flip, occupied_point, occupied_point] at he
  by_cases his : i ∈ s
  · rw [ite_eq_left his] at he
    right
    rw [he]
    exact ⟨Finset.erase_subset _ _, Finset.card_erase_add_one his⟩
  · rw [ite_eq_right his] at he
    left
    rw [he]
    exact ⟨Finset.subset_insert _ _, (Finset.card_insert_of_notMem his).symm⟩
private def neighbors (A : Finset Face) (s : Face) :=
  A.filter fun t => (hypercube 9).Adj (point s) (point t)
private theorem neighbors_card (C : Finset (Q 9)) (s : Face) :
    (neighbors (selected C) s).card = (directions C (point s)).card := by
  rw [directions_card]
  apply Finset.card_bij (fun t _ => point t)
  · intro t ht
    obtain ⟨ht, ha⟩ := Finset.mem_filter.mp ht
    exact Finset.mem_filter.mpr ⟨(mem_selected C t).mp ht, ha⟩
  · intro t _ u _ he
    exact point_injective he
  · intro x hx
    refine ⟨occupied x, ?_, point_occupied x⟩
    simpa [neighbors] using hx
private theorem selected_regular (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    {s : Face} (hs : s ∈ selected C) : (neighbors (selected C) s).card = 3 := by
  rw [neighbors_card]
  exact regular_directions C hr ((mem_selected C s).mp hs)
private theorem selected_exterior (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) {s : Face} (hs : s ∉ selected C) :
    Even (neighbors (selected C) s).card := by
  rw [neighbors_card]
  exact exterior_even C hr hb (point s) (by simpa using hs)

private theorem band_partition {A : Finset Face} {r : Nat}
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1) :
    layer A r ∪ layer A (r + 1) = A ∧ Disjoint (layer A r) (layer A (r + 1)) := by
  constructor
  · ext s; simp only [layer, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h; rcases hb s h with h0 | h1
      · exact Or.inl ⟨h, h0⟩
      · exact Or.inr ⟨h, h1⟩
  · apply Finset.disjoint_left.mpr
    intro s hs ht
    have h := (Finset.mem_filter.mp hs).2
    have h' := (Finset.mem_filter.mp ht).2
    omega

private theorem lower_neighbors {A : Finset Face} {r : Nat}
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1) {s : Face} (hs : s.card = r) :
    neighbors A s = (layer A (r + 1)).filter (s ⊆ ·) := by
  ext t
  simp only [neighbors, layer, Finset.mem_filter]
  constructor
  · rintro ⟨ht, ha⟩
    rcases adjacent_sets ha with ⟨hsub, hc⟩ | ⟨_, hc⟩
    · exact ⟨⟨ht, by omega⟩, hsub⟩
    · rcases hb t ht with h | h <;> omega
  · rintro ⟨⟨ht, hc⟩, hsub⟩
    exact ⟨ht, subset_succ_adj hsub (by omega)⟩

private theorem upper_neighbors {A : Finset Face} {r : Nat}
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1) {t : Face} (ht : t.card = r + 1) :
    neighbors A t = (layer A r).filter (· ⊆ t) := by
  ext s
  simp only [neighbors, layer, Finset.mem_filter]
  constructor
  · rintro ⟨hs, ha⟩
    rcases adjacent_sets ha with ⟨_, hc⟩ | ⟨hsub, hc⟩
    · rcases hb s hs with h | h <;> omega
    · exact ⟨⟨hs, by omega⟩, hsub⟩
  · rintro ⟨⟨hs, hc⟩, hsub⟩
    exact ⟨hs, (subset_succ_adj hsub (by omega)).symm⟩

private theorem band_handshake {A : Finset Face} {r : Nat}
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1)
    (hr : ∀ s ∈ A, (neighbors A s).card = 3) (hcard : A.card = 54) :
    (layer A r).card = 27 ∧ (layer A (r + 1)).card = 27 := by
  have hl (s : Face) (hs : s ∈ layer A r) :
      ((layer A (r + 1)).bipartiteAbove (· ⊆ ·) s).card = 3 := by
    change ((layer A (r + 1)).filter (s ⊆ ·)).card = 3
    rw [← lower_neighbors hb (Finset.mem_filter.mp hs).2]
    exact hr s (Finset.mem_filter.mp hs).1
  have hu (t : Face) (ht : t ∈ layer A (r + 1)) :
      ((layer A r).bipartiteBelow (· ⊆ ·) t).card = 3 := by
    change ((layer A r).filter (· ⊆ t)).card = 3
    rw [← upper_neighbors hb (Finset.mem_filter.mp ht).2]
    exact hr t (Finset.mem_filter.mp ht).1
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := layer A r) (t := layer A (r + 1)) (· ⊆ ·)
  rw [Finset.sum_congr rfl hl, Finset.sum_congr rfl hu] at he
  have hp := band_partition hb
  have hc := Finset.card_union_of_disjoint hp.2
  rw [hp.1, hcard] at hc
  simp only [Finset.sum_const, smul_eq_mul] at he
  omega


private def faces (r : Nat) : Finset Face := (Finset.univ : Face).powersetCard r
private def downDegree (F : Finset Face) (s : Face) := (F.filter (s ⊆ ·)).card
private def upDegree (F : Finset Face) (s : Face) := (F.filter (· ⊆ s)).card

private theorem faces_mem (r : Nat) (s : Face) : s ∈ faces r ↔ s.card = r := by
  simp [faces]

private theorem strict_inter {s t : Face} {r : Nat}
    (hs : s.card = r) (ht : t.card = r) (hne : s ≠ t) : (s ∩ t).card < r := by
  have hle := Finset.card_le_card (Finset.inter_subset_left : s ∩ t ⊆ s)
  by_contra h
  have he : s ∩ t = s := Finset.eq_of_subset_of_card_le
    Finset.inter_subset_left (by omega)
  have hsub : s ⊆ t := by rw [← he]; exact Finset.inter_subset_right
  exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))

private theorem strict_union {s t : Face} {r : Nat}
    (hs : s.card = r) (ht : t.card = r) (hne : s ≠ t) : r < (s ∪ t).card := by
  have hi := strict_inter hs ht hne
  have hc := Finset.card_union_add_card_inter s t
  omega

private theorem common_faces {s t : Face} {r : Nat} (hr : 0 < r)
    (hs : s.card = r) (ht : t.card = r) (hne : s ≠ t) :
    ((faces (r - 1)).filter (fun a => a ⊆ s ∧ a ⊆ t)).card =
      ((faces (r + 1)).filter (fun a => s ⊆ a ∧ t ⊆ a)).card := by
  have hi := strict_inter hs ht hne
  have hu := strict_union hs ht hne
  have hc := Finset.card_union_add_card_inter s t
  have hd : (faces (r - 1)).filter (fun a => a ⊆ s ∧ a ⊆ t) =
      if (s ∩ t).card = r - 1 then {s ∩ t} else ∅ := by
    ext a
    simp only [Finset.mem_filter, faces_mem]
    constructor
    · rintro ⟨ha, has, hat⟩
      have he : a = s ∩ t := Finset.eq_of_subset_of_card_le
        (Finset.subset_inter has hat) (by omega)
      subst a
      simp [ha]
    · split_ifs with he
      · intro ha
        have ha := Finset.mem_singleton.mp ha
        subst a
        exact ⟨he, Finset.inter_subset_left, Finset.inter_subset_right⟩
      · simp
  have hd' : (faces (r + 1)).filter (fun a => s ⊆ a ∧ t ⊆ a) =
      if (s ∪ t).card = r + 1 then {s ∪ t} else ∅ := by
    ext a
    simp only [Finset.mem_filter, faces_mem]
    constructor
    · rintro ⟨ha, has, hat⟩
      have he : s ∪ t = a := Finset.eq_of_subset_of_card_le
        (Finset.union_subset has hat) (by omega)
      subst a
      simp [ha]
    · split_ifs with he
      · intro ha
        have ha := Finset.mem_singleton.mp ha
        subst a
        exact ⟨he, Finset.subset_union_left, Finset.subset_union_right⟩
      · simp
  rw [hd, hd']
  have he : (s ∩ t).card = r - 1 ↔ (s ∪ t).card = r + 1 := by omega
  by_cases h : (s ∩ t).card = r - 1
  · simp [h, he.mp h]
  · have hn : (s ∪ t).card ≠ r + 1 := fun hu' => h (he.mpr hu')
    simp [h, hn]

private theorem pair_count {F : Finset Face} {r : Nat} (hr : 0 < r)
    (hF : ∀ s ∈ F, s.card = r) :
    (∑ a ∈ faces (r - 1), downDegree F a * (downDegree F a - 1)) =
      ∑ a ∈ faces (r + 1), upDegree F a * (upDegree F a - 1) := by
  have hd (a : Face) :
      (F.offDiag.filter (fun p => a ⊆ p.1 ∧ a ⊆ p.2)).card =
        downDegree F a * (downDegree F a - 1) := by
    have he : F.offDiag.filter (fun p => a ⊆ p.1 ∧ a ⊆ p.2) =
        (F.filter (a ⊆ ·)).offDiag := by ext p; simp; aesop
    rw [he, Finset.offDiag_card]
    dsimp [downDegree]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hu (a : Face) :
      (F.offDiag.filter (fun p => p.1 ⊆ a ∧ p.2 ⊆ a)).card =
        upDegree F a * (upDegree F a - 1) := by
    have he : F.offDiag.filter (fun p => p.1 ⊆ a ∧ p.2 ⊆ a) =
        (F.filter (· ⊆ a)).offDiag := by ext p; simp; aesop
    rw [he, Finset.offDiag_card]
    dsimp [upDegree]
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
  have hdown := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := faces (r - 1)) (t := F.offDiag) (fun a p => a ⊆ p.1 ∧ a ⊆ p.2)
  have hup := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := faces (r + 1)) (t := F.offDiag) (fun a p => p.1 ⊆ a ∧ p.2 ⊆ a)
  change (∑ a ∈ faces (r - 1), (F.offDiag.filter _).card) = _ at hdown
  change (∑ a ∈ faces (r + 1), (F.offDiag.filter _).card) = _ at hup
  rw [Finset.sum_congr rfl (fun a _ => hd a)] at hdown
  rw [Finset.sum_congr rfl (fun a _ => hu a)] at hup
  rw [hdown, hup]
  apply Finset.sum_congr rfl
  intro p hp
  obtain ⟨hs, ht, hn⟩ := Finset.mem_offDiag.mp hp
  exact common_faces hr (hF _ hs) (hF _ ht) hn

private theorem down_incidence {F : Finset Face} {r : Nat} (hr : 0 < r)
    (hF : ∀ s ∈ F, s.card = r) :
    (∑ a ∈ faces (r - 1), downDegree F a) = r * F.card := by
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := faces (r - 1)) (t := F) (· ⊆ ·)
  change (∑ a ∈ faces (r - 1), downDegree F a) = _ at he
  rw [he]
  have hf (s : Face) (hs : s ∈ F) :
      ((faces (r - 1)).bipartiteBelow (· ⊆ ·) s).card = r := by
    have he : (faces (r - 1)).bipartiteBelow (· ⊆ ·) s = s.powersetCard (r - 1) := by
      ext a
      simp [Finset.bipartiteBelow, faces_mem, and_comm]
    rw [he, Finset.card_powersetCard, hF s hs]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
    simp
  rw [Finset.sum_congr rfl hf]
  simp [Nat.mul_comm]

private theorem up_incidence {F : Finset Face} {r : Nat} (hr : r ≤ 9)
    (hF : ∀ s ∈ F, s.card = r) :
    (∑ a ∈ faces (r + 1), upDegree F a) = (9 - r) * F.card := by
  have he := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := faces (r + 1)) (t := F) (fun a s => s ⊆ a)
  change (∑ a ∈ faces (r + 1), upDegree F a) = _ at he
  rw [he]
  have hf (s : Face) (hs : s ∈ F) :
      ((faces (r + 1)).bipartiteBelow (fun a s => s ⊆ a) s).card = 9 - r := by
    change (((Finset.univ : Face).powersetCard (r + 1)).filter (s ⊆ ·)).card = _
    rw [Finset.card_filter_powersetCard_subset s Finset.univ (r + 1)
      (Finset.subset_univ _) (by rw [hF s hs]; omega)]
    simp [hF s hs]
  rw [Finset.sum_congr rfl hf]
  simp [Nat.mul_comm]


private theorem band_bounds {A : Finset Face} {r : Nat}
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1)
    (hreg : ∀ s ∈ A, (neighbors A s).card = 3)
    (hl : (layer A r).Nonempty) (hu : (layer A (r + 1)).Nonempty) :
    2 ≤ r ∧ r ≤ 6 := by
  obtain ⟨s, hs⟩ := hl
  obtain ⟨t, ht⟩ := hu
  obtain ⟨hsA, hsc⟩ := Finset.mem_filter.mp hs
  obtain ⟨htA, htc⟩ := Finset.mem_filter.mp ht
  have ht9 : t.card ≤ 9 := by simpa using Finset.card_le_univ t
  have hr9 : r ≤ 9 := by omega
  have hlow : (neighbors A s).card ≤ 9 - r := by
    rw [lower_neighbors hb hsc]
    have hsub : (layer A (r + 1)).filter (s ⊆ ·) ⊆
        (faces (r + 1)).filter (s ⊆ ·) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨(faces_mem _ _).mpr
        (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2,
        (Finset.mem_filter.mp ha).2⟩
    refine (Finset.card_le_card hsub).trans_eq ?_
    rw [faces, Finset.card_filter_powersetCard_subset s Finset.univ (r + 1)
      (Finset.subset_univ _) (by omega)]
    simp [hsc]
  have hupp : (neighbors A t).card ≤ r + 1 := by
    rw [upper_neighbors hb htc]
    have hsub : (layer A r).filter (· ⊆ t) ⊆ t.powersetCard r := by
      intro a ha
      exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp ha).2,
        (Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).2⟩
    refine (Finset.card_le_card hsub).trans_eq ?_
    simp [htc]
  rw [hreg s hsA] at hlow
  rw [hreg t htA] at hupp
  omega

private theorem below_neighbors {A : Finset Face} {r : Nat} (hr : 2 ≤ r)
    (hb : ∀ s ∈ A, s.card = r ∨ s.card = r + 1) {a : Face} (ha : a.card = r - 1) :
    neighbors A a = (layer A r).filter (a ⊆ ·) := by
  ext s
  simp only [neighbors, layer, Finset.mem_filter]
  constructor
  · rintro ⟨hs, hadj⟩
    rcases adjacent_sets hadj with ⟨hsub, hc⟩ | ⟨_, hc⟩
    · rcases hb s hs with h | h
      · exact ⟨⟨hs, h⟩, hsub⟩
      · omega
    · rcases hb s hs with h | h <;> omega
  · rintro ⟨⟨hs, hc⟩, hsub⟩
    exact ⟨hs, subset_succ_adj hsub (by omega)⟩

private theorem even_factorial_mod (a : Nat) (ha : Even a) :
    ((a * (a - 1) : Nat) : ZMod 8) = a := by
  have hres : a % 8 = 0 ∨ a % 8 = 2 ∨ a % 8 = 4 ∨ a % 8 = 6 := by
    obtain ⟨b, hb⟩ := ha
    omega
  have hpoly : (a : ZMod 8) * ((a : ZMod 8) - 1) = a := by
    have hc : (a : ZMod 8) = ((a % 8 : Nat) : ZMod 8) := (ZMod.natCast_mod a 8).symm
    simp only [hc]
    rcases hres with h | h | h | h <;> rw [h] <;> decide
  cases a with
  | zero => simp
  | succ a => simpa [Nat.cast_add, Nat.cast_mul] using hpoly

private theorem incidence_mod_eight {F G : Finset Face} {r : Nat}
    (hr : 2 ≤ r) (hr9 : r ≤ 9) (hF : ∀ s ∈ F, s.card = r)
    (hG : ∀ s ∈ G, s.card = r + 1)
    (hd : ∀ a ∈ faces (r - 1), Even (downDegree F a))
    (hm : ∀ a ∈ faces (r + 1),
      if a ∈ G then upDegree F a = 3 else Even (upDegree F a)) :
    (2 * r * F.card : ZMod 8) = (9 * F.card + 3 * G.card : ZMod 8) := by
  have hp := congrArg (fun a : Nat => (a : ZMod 8)) (pair_count (by omega) hF)
  simp only [Nat.cast_sum] at hp
  have hdown : (∑ a ∈ faces (r - 1),
      ((downDegree F a * (downDegree F a - 1) : Nat) : ZMod 8)) =
      (r * F.card : ZMod 8) := by
    calc
      _ = ∑ a ∈ faces (r - 1), (downDegree F a : ZMod 8) := by
        exact Finset.sum_congr rfl (fun a ha => even_factorial_mod _ (hd a ha))
      _ = _ := by
        simpa only [Nat.cast_sum, Nat.cast_mul] using
          congrArg (fun a : Nat => (a : ZMod 8)) (down_incidence (by omega) hF)
  have hupp : (∑ a ∈ faces (r + 1),
      ((upDegree F a * (upDegree F a - 1) : Nat) : ZMod 8)) =
      (((9 - r) * F.card : Nat) : ZMod 8) + 3 * G.card := by
    have hterm (a : Face) (ha : a ∈ faces (r + 1)) :
        ((upDegree F a * (upDegree F a - 1) : Nat) : ZMod 8) =
          (upDegree F a : ZMod 8) + if a ∈ G then 3 else 0 := by
      have hm' := hm a ha
      by_cases hag : a ∈ G
      · rw [ite_eq_left hag] at hm'
        rw [hm', ite_eq_left hag]
        norm_num
      · rw [ite_eq_right hag] at hm'
        rw [even_factorial_mod _ hm', ite_eq_right hag, add_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
    have hsum : (∑ a ∈ faces (r + 1), if a ∈ G then (3 : ZMod 8) else 0) =
        3 * G.card := by
      have he : (faces (r + 1)).filter (· ∈ G) = G := by
        ext a; simp only [Finset.mem_filter, faces_mem]
        exact ⟨And.right, fun ha => ⟨hG a ha, ha⟩⟩
      rw [← Finset.sum_filter, he]
      simp [mul_comm]
    rw [hsum]
    have hsum' : (∑ a ∈ faces (r + 1), (upDegree F a : ZMod 8)) =
        (((9 - r) * F.card : Nat) : ZMod 8) := by
      simpa only [Nat.cast_sum] using
        congrArg (fun a : Nat => (a : ZMod 8)) (up_incidence hr9 hF)
    rw [hsum']
  have hp' : (r * F.card : ZMod 8) =
      (((9 - r) * F.card : Nat) : ZMod 8) + 3 * G.card :=
    hdown.symm.trans (hp.trans hupp)
  have hsub : ((9 - r : Nat) : ZMod 8) = 9 - r := by
    rw [Nat.cast_sub hr9]; norm_num
  rw [Nat.cast_mul, hsub] at hp'
  calc
    (2 * r * F.card : ZMod 8) = r * F.card + r * F.card := by ring
    _ = ((9 - r) * F.card + 3 * G.card) + r * F.card := by rw [hp']
    _ = _ := by ring

private theorem pair_eq_of_mem_of_card {e : Face} {u v : Coord}
    (hu : u ∈ e) (hv : v ∈ e) (huv : u ≠ v) (he : e.card = 2) : e = {u, v} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset_iff.mpr ⟨hu, Finset.singleton_subset_iff.mpr hv⟩
  · simp [he, huv]

private def incidentNeighbors (E : Finset Face) (v : Coord) : Finset Coord :=
  (E.filter (v ∈ ·)).biUnion (fun e => e.erase v)

private theorem incidentNeighbors_mem_iff {E : Finset Face} {v w : Coord} :
    w ∈ incidentNeighbors E v ↔ ∃ e ∈ E, v ∈ e ∧ w ∈ e ∧ w ≠ v := by
  simp only [incidentNeighbors, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨e, ⟨he, hv⟩, ⟨hne, hw⟩⟩
    exact ⟨e, he, hv, hw, hne⟩
  · rintro ⟨e, he, hv, hw, hne⟩
    exact ⟨e, ⟨he, hv⟩, ⟨hne, hw⟩⟩

private theorem incidentNeighbors_card {E : Finset Face} (v : Coord)
    (hE : ∀ e ∈ E, e.card = 2) :
    (incidentNeighbors E v).card = (E.filter (v ∈ ·)).card := by
  have hdis : (↑(E.filter (v ∈ ·)) : Set Face).PairwiseDisjoint
      (fun e => e.erase v) := by
    intro e he f hf hne
    apply Finset.disjoint_left.mpr
    intro w hwe hwf
    have hwe' := Finset.mem_erase.mp hwe
    have hwf' := Finset.mem_erase.mp hwf
    have hev : v ∈ e := (Finset.mem_filter.mp he).2
    have hfv : v ∈ f := (Finset.mem_filter.mp hf).2
    have hef : e = {v, w} := pair_eq_of_mem_of_card hev hwe'.2 hwe'.1.symm
      (hE e (Finset.mem_filter.mp he).1)
    have hff : f = {v, w} := pair_eq_of_mem_of_card hfv hwf'.2 hwf'.1.symm
      (hE f (Finset.mem_filter.mp hf).1)
    exact hne (hef.trans hff.symm)
  rw [show incidentNeighbors E v = (E.filter (v ∈ ·)).biUnion (fun e => e.erase v) by rfl,
    Finset.card_biUnion hdis]
  rw [Finset.sum_filter]
  have hterm : ∀ e ∈ E,
      (if v ∈ e then (e.erase v).card else 0) = (if v ∈ e then 1 else 0) := by
    intro e he
    by_cases hv : v ∈ e
    · simp [hv, Finset.card_erase_of_mem hv, hE e he]
    · simp [hv]
  rw [Finset.sum_congr rfl hterm]
  rw [Finset.card_filter]

private theorem triple_eq_of_subset_of_card {t : Face} {u v w : Coord}
    (hu : u ∈ t) (hv : v ∈ t) (hw : w ∈ t)
    (hcard : t.card = 3) (hpair : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    t = {u, v, w} := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · exact Finset.insert_subset_iff.mpr ⟨hu, Finset.insert_subset_iff.mpr
      ⟨hv, Finset.singleton_subset_iff.mpr hw⟩⟩
  · rw [Finset.card_triple_eq_three_iff.mpr ⟨hpair, huw, hvw⟩, hcard]

private def pairGraph (F : Finset Face) : SimpleGraph Coord where
  Adj u v := u ≠ v ∧ ({u, v} : Face) ∈ F
  symm := ⟨by intro u v h; exact ⟨h.1.symm, by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨by intro u h; exact h.1 rfl⟩

private theorem pairGraph_neighbors {F : Finset Face} (hF : ∀ e ∈ F, e.card = 2)
    (u : Coord) : (pairGraph F).neighborFinset u = incidentNeighbors F u := by
  ext v
  rw [SimpleGraph.mem_neighborFinset, incidentNeighbors_mem_iff]
  constructor
  · rintro ⟨hne, he⟩
    exact ⟨{u, v}, he, by simp, by simp, hne.symm⟩
  · rintro ⟨e, he, hu, hv, hne⟩
    exact ⟨hne.symm, pair_eq_of_mem_of_card hu hv hne.symm (hF e he) ▸ he⟩

private theorem selected_triple_faces {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3) {t : Face} (ht : t ∈ G) :
    t.powersetCard 2 ⊆ F := by
  have hs : F.filter (· ⊆ t) ⊆ t.powersetCard 2 := by
    intro e he
    exact Finset.mem_powersetCard.mpr ⟨(Finset.mem_filter.mp he).2,
      hF e (Finset.mem_filter.mp he).1⟩
  have he : F.filter (· ⊆ t) = t.powersetCard 2 := by
    apply Finset.eq_of_subset_of_card_le hs
    rw [Finset.card_powersetCard, hG t ht]
    change 3 ≤ upDegree F t
    rw [hupper t ht]
  rw [← he]
  exact Finset.filter_subset _ _

private theorem triple_faces_selected {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    {t : Face} (ht : t.card = 3) (hall : t.powersetCard 2 ⊆ F) : t ∈ G := by
  by_contra hn
  have he : F.filter (· ⊆ t) = t.powersetCard 2 := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨fun h => ⟨h.2, hF e h.1⟩, fun h => ⟨hall (Finset.mem_powersetCard.mpr h), h.1⟩⟩
  have h := hext t ht hn
  change Even (F.filter (· ⊆ t)).card at h
  rw [he, Finset.card_powersetCard, ht] at h
  norm_num at h

private theorem pair_subsets_triple {e : Face} {u v w : Coord}
    (he : e.card = 2) (hsub : e ⊆ ({u, v, w} : Face)) :
    e = {u, v} ∨ e = {u, w} ∨ e = {v, w} := by
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp he
  have ha := hsub (show a ∈ ({a, b} : Face) by simp)
  have hb := hsub (show b ∈ ({a, b} : Face) by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    simp_all [Finset.pair_comm]

private theorem no_edge_isolate {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2)
    (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    {u v w : Coord} (huv : (pairGraph F).Adj u v) (huw : u ≠ w) (hvw : v ≠ w) :
    (pairGraph F).Adj u w ∨ (pairGraph F).Adj v w := by
  by_contra hn
  have huwn : ({u, w} : Face) ∉ F := fun h => hn (Or.inl ⟨huw, h⟩)
  have hvwn : ({v, w} : Face) ∉ F := fun h => hn (Or.inr ⟨hvw, h⟩)
  have hcard : ({u, v, w} : Face).card = 3 :=
    Finset.card_triple_eq_three_iff.mpr ⟨huv.1, huw, hvw⟩
  have he : F.filter (· ⊆ ({u, v, w} : Face)) = {{u, v}} := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨he, hs⟩
      rcases pair_subsets_triple (hF e he) hs with h | h | h
      · exact h
      · exact (huwn (h ▸ he)).elim
      · exact (hvwn (h ▸ he)).elim
    · rintro rfl
      exact ⟨huv.2, by simp⟩
  have hd : upDegree F ({u, v, w} : Face) = 1 := by
    dsimp [upDegree]; rw [he]; simp
  by_cases ht : ({u, v, w} : Face) ∈ G
  · have h := hupper _ ht; omega
  · have h := hext _ hcard ht; rw [hd] at h; norm_num at h

private theorem triple_diff_card {t e : Face} (ht : t.card = 3) (he : e.card = 2)
    (hsub : e ⊆ t) : (t \ e).card = 1 := by
  rw [Finset.card_sdiff_of_subset hsub, ht, he]

private def upperCommon (G : Finset Face) (u v : Coord) : Finset Coord :=
  (G.filter ({u, v} ⊆ ·)).biUnion (fun t => t \ {u, v})

private theorem upperCommon_card {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ e ∈ F, (G.filter (e ⊆ ·)).card = 3)
    (u v : Coord) (huv : (pairGraph F).Adj u v) :
    (upperCommon G u v).card = 3 := by
  have hp : ({u, v} : Face) ∈ F := huv.2
  have hcnt : (G.filter ({u, v} ⊆ ·)).card = 3 := hupper _ hp
  have hdis : (↑(G.filter ({u, v} ⊆ ·)) : Set Face).PairwiseDisjoint
      (fun t => t \ {u, v}) := by
    intro t ht s hs hne
    apply Finset.disjoint_left.mpr
    intro w hwt hws
    have hwt' := Finset.mem_sdiff.mp hwt
    have hws' := Finset.mem_sdiff.mp hws
    have huw : u ≠ w := by
      intro h; exact hwt'.2 (by simp [h])
    have hvw : v ≠ w := by
      intro h; exact hwt'.2 (by simp [h])
    have hts : t = {u, v, w} := triple_eq_of_subset_of_card
      ((Finset.mem_filter.mp ht).2 (by simp))
      ((Finset.mem_filter.mp ht).2 (by simp)) hwt'.1
      (hG t (Finset.mem_filter.mp ht).1) huv.1 huw hvw
    have hst : s = {u, v, w} := triple_eq_of_subset_of_card
      ((Finset.mem_filter.mp hs).2 (by simp))
      ((Finset.mem_filter.mp hs).2 (by simp)) hws'.1
      (hG s (Finset.mem_filter.mp hs).1) huv.1 huw hvw
    exact hne (hts.trans hst.symm)
  rw [show upperCommon G u v =
      (G.filter ({u, v} ⊆ ·)).biUnion (fun t => t \ {u, v}) by rfl,
    Finset.card_biUnion hdis]
  have hterm (t : Face) (ht : t ∈ G.filter ({u, v} ⊆ ·)) :
      (t \ {u, v}).card = 1 := by
    apply triple_diff_card (hG t (Finset.mem_filter.mp ht).1)
      (Finset.card_pair huv.1) (Finset.mem_filter.mp ht).2
  rw [Finset.sum_congr rfl hterm]
  simp [hcnt]

private theorem triangle_iff {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    {u v w : Coord} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ({u, v, w} : Face) ∈ G ↔
      (pairGraph F).Adj u v ∧ (pairGraph F).Adj u w ∧ (pairGraph F).Adj v w := by
  constructor
  · intro ht
    have hs := selected_triple_faces hF hG hupper ht
    refine ⟨⟨huv, hs ?_⟩, ⟨huw, hs ?_⟩, ⟨hvw, hs ?_⟩⟩ <;>
      apply Finset.mem_powersetCard.mpr <;> constructor
    · simp
    · exact Finset.card_pair huv
    · simp
    · exact Finset.card_pair huw
    · simp
    · exact Finset.card_pair hvw
  · rintro ⟨huv', huw', hvw'⟩
    apply triple_faces_selected hF hext (Finset.card_triple_eq_three_iff.mpr ⟨huv, huw, hvw⟩)
    intro e he
    rcases pair_subsets_triple (Finset.mem_powersetCard.mp he).2
      (Finset.mem_powersetCard.mp he).1 with rfl | rfl | rfl
    · exact huv'.2
    · exact huw'.2
    · exact hvw'.2

private theorem upperCommon_eq {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    {u v : Coord} (huv : (pairGraph F).Adj u v) :
    upperCommon G u v = (pairGraph F).neighborFinset u ∩ (pairGraph F).neighborFinset v := by
  ext w
  simp only [upperCommon, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_sdiff, Finset.mem_inter, SimpleGraph.mem_neighborFinset]
  constructor
  · rintro ⟨t, ⟨ht, hsub⟩, hwt, hwn⟩
    have huw : u ≠ w := by intro h; exact hwn (by simp [h])
    have hvw : v ≠ w := by intro h; exact hwn (by simp [h])
    have he := triple_eq_of_subset_of_card (hsub (by simp)) (hsub (by simp)) hwt
      (hG t ht) huv.1 huw hvw
    rw [he] at ht
    exact ((triangle_iff hF hG hupper hext huv.1 huw hvw).mp ht).2
  · rintro ⟨huw, hvw⟩
    refine ⟨{u, v, w}, ⟨?_, by simp⟩, by simp, ?_⟩
    · exact (triangle_iff hF hG hupper hext huv.1 huw.1 hvw.1).mpr ⟨huv, huw, hvw⟩
    · simp [huw.1.symm, hvw.1.symm]

private theorem pairGraph_degree_sum {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hlower : ∀ e ∈ F, (G.filter (e ⊆ ·)).card = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    {u v : Coord} (huv : (pairGraph F).Adj u v) :
    (pairGraph F).degree u + (pairGraph F).degree v = 12 := by
  have hcover : (pairGraph F).neighborFinset u ∪ (pairGraph F).neighborFinset v = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro w
    by_cases hwu : w = u
    · subst w; exact Finset.mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr huv.symm)
    by_cases hwv : w = v
    · subst w; exact Finset.mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr huv)
    rcases no_edge_isolate hF hG hupper hext huv (fun h => hwu h.symm) (fun h => hwv h.symm) with h | h
    · exact Finset.mem_union_left _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)
    · exact Finset.mem_union_right _ ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)
  have hcommon : ((pairGraph F).neighborFinset u ∩ (pairGraph F).neighborFinset v).card = 3 := by
    rw [← upperCommon_eq hF hG hupper hext huv]
    exact upperCommon_card hF hG hlower u v huv
  have h := Finset.card_union_add_card_inter
    ((pairGraph F).neighborFinset u) ((pairGraph F).neighborFinset v)
  rw [hcover, hcommon, Finset.card_univ, Fintype.card_fin,
    SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.card_neighborFinset_eq_degree] at h
  omega

private theorem pairGraph_regular {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hlower : ∀ e ∈ F, (G.filter (e ⊆ ·)).card = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    (hFn : F.Nonempty) (v : Coord) : (pairGraph F).degree v = 6 := by
  obtain ⟨e, he⟩ := hFn
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (hF e he)
  have hab' : (pairGraph F).Adj a b := ⟨hab, he⟩
  have hneighbor : ∃ w, (pairGraph F).Adj v w := by
    by_cases hva : v = a
    · exact ⟨b, hva ▸ hab'⟩
    by_cases hvb : v = b
    · exact ⟨a, hvb ▸ hab'.symm⟩
    rcases no_edge_isolate hF hG hupper hext hab' (fun h => hva h.symm) (fun h => hvb h.symm) with h | h
    · exact ⟨a, h.symm⟩
    · exact ⟨b, h.symm⟩
  obtain ⟨w, hvw⟩ := hneighbor
  have hcommon := upperCommon_card hF hG hlower v w hvw
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (by omega : 0 < (upperCommon G v w).card)
  rw [upperCommon_eq hF hG hupper hext hvw] at hz
  obtain ⟨hvz, hwz⟩ := Finset.mem_inter.mp hz
  have hvz := (SimpleGraph.mem_neighborFinset _ _ _).mp hvz
  have hwz := (SimpleGraph.mem_neighborFinset _ _ _).mp hwz
  have h1 := pairGraph_degree_sum hF hG hupper hlower hext hvw
  have h2 := pairGraph_degree_sum hF hG hupper hlower hext hvz
  have h3 := pairGraph_degree_sum hF hG hupper hlower hext hwz
  omega

private theorem coordinate_triangles {F G : Finset Face}
    (hF : ∀ e ∈ F, e.card = 2) (hG : ∀ t ∈ G, t.card = 3)
    (hupper : ∀ t ∈ G, upDegree F t = 3)
    (hlower : ∀ e ∈ F, (G.filter (e ⊆ ·)).card = 3)
    (hext : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t))
    (hFn : F.Nonempty) (v : Coord) : (G.filter (v ∈ ·)).card = 9 := by
  let H := pairGraph F
  have hdeg : (H.neighborFinset v).card = 6 := by
    rw [SimpleGraph.card_neighborFinset_eq_degree]
    exact pairGraph_regular hF hG hupper hlower hext hFn v
  have hwcount (w : Coord) (hw : w ∈ H.neighborFinset v) :
      ((G.filter (v ∈ ·)).bipartiteAbove (fun w t => w ∈ t) w).card = 3 := by
    have hvw : H.Adj v w := (SimpleGraph.mem_neighborFinset _ _ _).mp hw
    have hset : (G.filter (v ∈ ·)).bipartiteAbove (fun w t => w ∈ t) w =
        G.filter ({v, w} ⊆ ·) := by
      ext t
      simp [Finset.bipartiteAbove, Finset.insert_subset_iff, and_assoc]
    rw [hset]
    exact hlower _ hvw.2
  have htcount (t : Face) (ht : t ∈ G.filter (v ∈ ·)) :
      ((H.neighborFinset v).bipartiteBelow (fun w t => w ∈ t) t).card = 2 := by
    have hv := (Finset.mem_filter.mp ht).2
    have htG := (Finset.mem_filter.mp ht).1
    have hset : (H.neighborFinset v).bipartiteBelow (fun w t => w ∈ t) t = t.erase v := by
      ext w
      simp only [Finset.mem_bipartiteBelow, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
      constructor
      · rintro ⟨hvw, hwt⟩
        exact ⟨hvw.1.symm, hwt⟩
      · rintro ⟨hwv, hwt⟩
        refine ⟨⟨hwv.symm, ?_⟩, hwt⟩
        apply selected_triple_faces hF hG hupper htG
        apply Finset.mem_powersetCard.mpr
        constructor
        · intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl
          · exact hv
          · exact hwt
        · exact Finset.card_pair hwv.symm
    rw [hset, Finset.card_erase_of_mem hv, hG t htG]
  have h := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := H.neighborFinset v) (t := G.filter (v ∈ ·)) (fun w t => w ∈ t)
  rw [Finset.sum_congr rfl hwcount, Finset.sum_congr rfl htcount] at h
  simp only [Finset.sum_const, smul_eq_mul, hdeg] at h
  omega

private theorem two_three_half {A : Finset Face}
    (hband : ∀ s ∈ A, s.card = 2 ∨ s.card = 3)
    (hreg : ∀ s ∈ A, (neighbors A s).card = 3)
    (hext : ∀ s ∉ A, Even (neighbors A s).card)
    (hcard : A.card = 54) (v : Coord) : (A.filter (v ∈ ·)).card = 15 := by
  let F := layer A 2
  let G := layer A 3
  have hF : ∀ e ∈ F, e.card = 2 := fun e he => (Finset.mem_filter.mp he).2
  have hG : ∀ t ∈ G, t.card = 3 := fun t ht => (Finset.mem_filter.mp ht).2
  have hupper : ∀ t ∈ G, upDegree F t = 3 := by
    intro t ht
    have h := hreg t (Finset.mem_filter.mp ht).1
    rwa [upper_neighbors hband (hG t ht)] at h
  have hlower : ∀ e ∈ F, (G.filter (e ⊆ ·)).card = 3 := by
    intro e he
    have h := hreg e (Finset.mem_filter.mp he).1
    rwa [lower_neighbors hband (hF e he)] at h
  have hparity : ∀ t : Face, t.card = 3 → t ∉ G → Even (upDegree F t) := by
    intro t ht hn
    have hnA : t ∉ A := fun h => hn (Finset.mem_filter.mpr ⟨h, ht⟩)
    have h := hext t hnA
    rwa [upper_neighbors hband ht] at h
  have hFcard : F.card = 27 := (band_handshake hband hreg hcard).1
  have hFn : F.Nonempty := Finset.card_pos.mp (by omega)
  have hpairs : (F.filter (v ∈ ·)).card = 6 := by
    rw [← incidentNeighbors_card v hF, ← pairGraph_neighbors hF v,
      SimpleGraph.card_neighborFinset_eq_degree]
    exact pairGraph_regular hF hG hupper hlower hparity hFn v
  have htriples : (G.filter (v ∈ ·)).card = 9 :=
    coordinate_triangles hF hG hupper hlower hparity hFn v
  have hpart := band_partition hband
  have hset : A.filter (v ∈ ·) = F.filter (v ∈ ·) ∪ G.filter (v ∈ ·) := by
    rw [← hpart.1, Finset.filter_union]
  rw [hset, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hpart.2), hpairs, htriples]

private theorem complement_adj (s t : Face) :
    (hypercube 9).Adj (point sᶜ) (point tᶜ) ↔ (hypercube 9).Adj (point s) (point t) := by
  change (Finset.univ.filter (fun i => point sᶜ i ≠ point tᶜ i)).card = 1 ↔
    (Finset.univ.filter (fun i => point s i ≠ point t i)).card = 1
  have he : (Finset.univ.filter (fun i => point sᶜ i ≠ point tᶜ i)) =
      (Finset.univ.filter (fun i => point s i ≠ point t i)) := by
    ext i
    simp [point]
  rw [he]

private theorem complement_neighbors (A : Finset Face) (s : Face) :
    (neighbors (A.image (fun t => tᶜ)) sᶜ).card = (neighbors A s).card := by
  apply Finset.card_bij (fun t _ => tᶜ)
  · intro t ht
    obtain ⟨ht, hadj⟩ := Finset.mem_filter.mp ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨by simpa using hu, by
      simpa using (complement_adj s u).mp hadj⟩
  · intro t _ u _ h
    exact compl_injective h
  · intro t ht
    refine ⟨tᶜ, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨t,
      (Finset.mem_filter.mp ht).1, rfl⟩,
      (complement_adj s t).mpr (Finset.mem_filter.mp ht).2⟩, ?_⟩
    simp

private theorem six_seven_half {A : Finset Face}
    (hband : ∀ s ∈ A, s.card = 6 ∨ s.card = 7)
    (hreg : ∀ s ∈ A, (neighbors A s).card = 3)
    (hext : ∀ s ∉ A, Even (neighbors A s).card)
    (hcard : A.card = 54) (v : Coord) : (A.filter (v ∉ ·)).card = 15 := by
  let B := A.image (fun s => sᶜ)
  have hB : ∀ s ∈ B, s.card = 2 ∨ s.card = 3 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    have h := hband t ht
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  have hBreg : ∀ s ∈ B, (neighbors B s).card = 3 := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
    rw [complement_neighbors]
    exact hreg t ht
  have hBext : ∀ s ∉ B, Even (neighbors B s).card := by
    intro s hs
    have hn : sᶜ ∉ A := by
      intro h
      exact hs (Finset.mem_image.mpr ⟨sᶜ, h, by simp⟩)
    have h := hext sᶜ hn
    have he' : (neighbors B s).card = (neighbors A sᶜ).card := by
      simpa using (complement_neighbors A sᶜ)
    exact he'.symm ▸ h
  have hBc : B.card = 54 := (Finset.card_image_of_injective _ compl_injective).trans hcard
  have h := two_three_half hB hBreg hBext hBc v
  have he : (B.filter (v ∈ ·)).card = (A.filter (v ∉ ·)).card := by
    apply Finset.card_bij (fun s _ => sᶜ)
    · intro s hs
      obtain ⟨hsB, hv⟩ := Finset.mem_filter.mp hs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hsB
      exact Finset.mem_filter.mpr ⟨by simpa using ht, by simpa using hv⟩
    · intro s _ t _ he
      exact compl_injective he
    · intro s hs
      refine ⟨sᶜ, Finset.mem_filter.mpr ⟨Finset.mem_image.mpr
        ⟨s, (Finset.mem_filter.mp hs).1, rfl⟩, ?_⟩, by simp⟩
      simpa using (Finset.mem_filter.mp hs).2
  rwa [he] at h

private theorem slice_card_selected (C : Finset (Q 9)) (b : Bool) :
    (coordinateSlice C b).card =
      ((selected C).filter (fun s => (0 : Coord) ∈ s ↔ b = true)).card := by
  apply Finset.card_bij (fun x _ => occupied x)
  · intro x hx
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x, (Finset.mem_filter.mp hx).1, rfl⟩, ?_⟩
    cases b <;> simp [mem_occupied, (Finset.mem_filter.mp hx).2]
  · intro x _ y _ hxy
    exact occupied_injective hxy
  · intro s hs
    have hsC := (mem_selected C s).mp (Finset.mem_filter.mp hs).1
    refine ⟨point s, Finset.mem_filter.mpr ⟨hsC, ?_⟩, ?_⟩
    · cases b <;> simpa [point] using (Finset.mem_filter.mp hs).2
    · simp

private theorem adjacent_slice_card {C : Finset (Q 9)}
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) (r : Nat)
    (hband : ∀ x ∈ C, (occupied x).card = r ∨ (occupied x).card = r + 1)
    (hrigid : r = 2 ∨ r = 6) :
    (if r = 2 then (coordinateSlice C true).card else (coordinateSlice C false).card) = 15 := by
  let A := selected C
  have hA : ∀ s ∈ A, s.card = r ∨ s.card = r + 1 := by
    intro s hs
    simpa using hband (point s) ((mem_selected C s).mp hs)
  have hreg : ∀ s ∈ A, (neighbors A s).card = 3 := fun s hs => selected_regular C hr hs
  have hc : A.card = 54 := (card_selected C).trans hcard
  have hext : ∀ s ∉ A, Even (neighbors A s).card := fun s hs => selected_exterior C hr hb hs
  rcases hrigid with rfl | rfl
  · simp only [ite_eq_left rfl]
    rw [slice_card_selected]
    simpa using two_three_half hA hreg hext hc 0
  · simp only [ite_eq_right (by decide : (6 : Nat) ≠ 2)]
    rw [slice_card_selected]
    simpa using six_seven_half hA hreg hext hc 0

private theorem band_rigidity (C : Finset (Q 9))
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) (r : Nat)
    (hband : ∀ x ∈ C, (occupied x).card = r ∨ (occupied x).card = r + 1) :
    r = 2 ∨ r = 6 := by
  let A := selected C
  have hA : ∀ s ∈ A, s.card = r ∨ s.card = r + 1 := by
    intro s hs
    have hh := hband (point s) ((mem_selected C s).mp hs)
    simpa using hh
  have hreg : ∀ s ∈ A, (neighbors A s).card = 3 := fun s hs => selected_regular C hr hs
  have hc : A.card = 54 := (card_selected C).trans hcard
  obtain ⟨hl, hu⟩ := band_handshake hA hreg hc
  obtain ⟨hr2, hr6⟩ := band_bounds hA hreg
    (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
  have hd (a : Face) (ha : a ∈ faces (r - 1)) : Even (downDegree (layer A r) a) := by
    have hac := (faces_mem _ _).mp ha
    have han : a ∉ selected C := by intro hh; rcases hA a hh with hh | hh <;> omega
    have he := selected_exterior C hr hb han
    rwa [below_neighbors hr2 hA hac] at he
  have hm (a : Face) (ha : a ∈ faces (r + 1)) :
      if a ∈ layer A (r + 1) then upDegree (layer A r) a = 3
      else Even (upDegree (layer A r) a) := by
    have hac := (faces_mem _ _).mp ha
    by_cases hag : a ∈ layer A (r + 1)
    · rw [ite_eq_left hag]
      have he := hreg a (Finset.mem_filter.mp hag).1
      rwa [upper_neighbors hA hac] at he
    · rw [ite_eq_right hag]
      have han : a ∉ selected C := by intro hh; exact hag (Finset.mem_filter.mpr ⟨hh, hac⟩)
      have he := selected_exterior C hr hb han
      rwa [upper_neighbors hA hac] at he
  have he := incidence_mod_eight hr2 (by omega)
    (fun s hs => (Finset.mem_filter.mp hs).2)
    (fun s hs => (Finset.mem_filter.mp hs).2) hd hm
  change (2 * r * (layer A r).card : ZMod 8) =
    (9 * (layer A r).card + 3 * (layer A (r + 1)).card : ZMod 8) at he
  rw [hl, hu] at he
  have he' : ((54 * r : Nat) : ZMod 8) = (324 : Nat) := by
    push_cast
    convert he using 1 <;> ring
  have hc' : (54 * r) % 8 = 324 % 8 :=
    (ZMod.natCast_eq_natCast_iff' _ _ 8).mp he'
  omega

/-- Actual adjacent Hamming layers force total cube-symmetry reconstruction. -/
theorem adjacent_layers_gray_reconstruction {C : Finset (Q 9)}
    (hC : C.Nonempty)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C) (hcard : C.card = 54) (r : Nat)
    (hband : ∀ x ∈ C, (Finset.univ.filter (fun i => x i = true)).card = r ∨
      (Finset.univ.filter (fun i => x i = true)).card = r + 1) :
    ∃ (g : Q 9 ≃ Q 9) (pi : Fin 9 ≃ Fin 9),
      (∀ x i, g (BalancedCriticalSpectrum.flip x i) =
        BalancedCriticalSpectrum.flip (g x) (pi i)) ∧
      C = (GrayGridComponent.support 3).image g := by
  have hrigid := band_rigidity C hr hb hcard r hband
  have hs := adjacent_slice_card hr hb hcard r hband hrigid
  rcases hrigid with h2 | h6
  · subst r
    have hs15 : (coordinateSlice C true).card = 15 := by simpa using hs
    exact ThinSliceGrayReconstruction.thin_slice_gray_reconstruction hC hr hb true (by omega)
  · subst r
    have hs15 : (coordinateSlice C false).card = 15 := by simpa using hs
    exact ThinSliceGrayReconstruction.thin_slice_gray_reconstruction hC hr hb false (by omega)


#print axioms adjacent_layers_gray_reconstruction

end D5.S3.Combinatorics.Graph.HypercubeCritical.AdjacentLayerRigidity
