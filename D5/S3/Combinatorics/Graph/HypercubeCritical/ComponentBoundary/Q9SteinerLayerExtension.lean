/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9SteinerLayerExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting, mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Tactic.Tauto]
   utility: none
   digest: Steiner reconstruction gives the unique 246-point subcubic extension of a maximal cubic support on layers three and four. -/

import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Tauto
import Batteries.Tactic.OpenPrivate
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LevelThreeFourObstruction

/-!
The subset model reconstructs the Steiner triple system and the closed neighborhood.
If each middle layer has `k` selected sites, selected triples have `3k` incidences
with the `126 - k` omitted fours. Each omitted four accounts for at most four
incidences, so `k ≤ 72` before using the total size 144 to force equality.

The residual layers are 0, 1, 6, 7, 8 and 9. If a subcubic residual subset keeps
`k` layer-7 sites and omits `d₆` layer-6 sites, then `4k ≤ 3d₆`.
This gives `d₆ + 36 - k ≥ 36`, with strict inequality for positive `k`.
Each of the two residual stars needs one more deletion and needs at least six
if its center is retained. The unique extension of size 246 adds layers 1, 6 and 8.
The final two theorems state the upper bound and equality case in the Boolean cube.
-/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension

open Finset
open scoped BigOperators

abbrev Face := Finset (Fin 9)
abbrev faces (k : ℕ) : Finset Face := (univ : Face).powersetCard k

@[simp] private theorem mem_faces {s : Face} {k : ℕ} : s ∈ faces k ↔ s.card = k := by
  simp [faces]

private theorem card_faces (k : ℕ) : (faces k).card = Nat.choose 9 k := by
  simp [faces, card_powersetCard]

/-- Cube adjacency in the subset representation. -/
def Adj (s t : Face) : Prop :=
  (s ⊆ t ∧ s.card + 1 = t.card) ∨ (t ⊆ s ∧ t.card + 1 = s.card)

instance (s t : Face) : Decidable (Adj s t) := by
  unfold Adj
  infer_instance

private theorem adj_comm {s t : Face} : Adj s t ↔ Adj t s := by
  unfold Adj
  tauto

abbrev neighbors (S : Finset Face) (s : Face) : Finset Face := S.filter (Adj s)
abbrev above (S : Finset Face) (s : Face) : Finset Face := S.filter (s ⊆ ·)
abbrev below (S : Finset Face) (s : Face) : Finset Face := S.filter (· ⊆ s)

private theorem card_above_faces {s : Face} {k : ℕ} (h : s.card ≤ k) :
    (above (faces k) s).card = Nat.choose (9 - s.card) (k - s.card) := by
  simpa [above, faces] using card_filter_powersetCard_subset s univ k (subset_univ _) h

private theorem below_faces (s : Face) (k : ℕ) :
    below (faces k) s = s.powersetCard k := by
  ext t
  simp only [mem_filter, mem_powersetCard, subset_univ, true_and, and_comm]

private theorem card_filter_complement {α : Type*} [DecidableEq α]
    {T S : Finset α} (h : T ⊆ S) (P : α → Prop) [DecidablePred P] :
    ((S \ T).filter P).card + (T.filter P).card = (S.filter P).card := by
  have he : (S \ T).filter P = S.filter P \ T.filter P := by
    ext x
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [he, card_sdiff_add_card_eq_card (filter_subset_filter P h)]

private theorem eq_const_of_sum_eq {α : Type*}
    {S : Finset α} {f : α → ℕ} {k : ℕ}
    (hle : ∀ x ∈ S, f x ≤ k) (hsum : (∑ x ∈ S, f x) = S.card * k)
    {x : α} (hx : x ∈ S) : f x = k := by
  classical
  have hrest : (∑ y ∈ S.erase x, f y) ≤ (S.erase x).card * k := by
    calc
      _ ≤ ∑ _y ∈ S.erase x, k := sum_le_sum fun y hy => hle y (mem_erase.mp hy).2
      _ = _ := by simp
  have hsplit := sum_erase_add S f hx
  rw [hsum, ← card_erase_add_one hx, Nat.add_mul, Nat.one_mul] at hsplit
  have := hle x hx
  omega

private theorem band_neighbors {C : Finset Face} {s : Face} {k : ℕ}
    (hC : ∀ t ∈ C, t.card = k ∨ t.card = k + 1) :
    (s.card = k → neighbors C s = above (C ∩ faces (k + 1)) s) ∧
    (s.card = k + 1 → neighbors C s = below (C ∩ faces k) s) := by
  constructor <;> intro hs <;> ext t <;>
    simp only [mem_filter, mem_inter, mem_faces, Adj]
  · constructor
    · rintro ⟨ht, ⟨hst, he⟩ | ⟨_, he⟩⟩
      · exact ⟨⟨ht, by omega⟩, hst⟩
      · rcases hC t ht with h | h <;> omega
    · rintro ⟨⟨ht, he⟩, hst⟩
      exact ⟨ht, Or.inl ⟨hst, by omega⟩⟩
  · constructor
    · rintro ⟨ht, ⟨_, he⟩ | ⟨hts, he⟩⟩
      · rcases hC t ht with h | h <;> omega
      · exact ⟨⟨ht, by omega⟩, hts⟩
    · rintro ⟨⟨ht, he⟩, hts⟩
      exact ⟨ht, Or.inr ⟨hts, by omega⟩⟩

/-- The triples omitted from the support. -/
abbrev missingTriples (C : Finset Face) : Finset Face := faces 3 \ C

set_option maxHeartbeats 1200000 in
/-- The omitted triples form a Steiner triple system. A four-set contains a
missing triple exactly when it is selected, and then contains just one. -/
theorem missing_triples_steiner {C : Finset Face} (hcard : C.card = 144)
    (hband : ∀ s ∈ C, s.card = 3 ∨ s.card = 4)
    (hcubic : ∀ s ∈ C, (neighbors C s).card = 3) :
    (missingTriples C).card = 12 ∧
    (∀ p ∈ faces 2, (above (missingTriples C) p).card = 1) ∧
    ∀ u ∈ faces 4, (below (missingTriples C) u).card = if u ∈ C then 1 else 0 := by
  let T := C ∩ faces 3
  let U := C ∩ faces 4
  let W := faces 4 \ U
  let M := faces 3 \ T
  have hT : T ⊆ faces 3 := inter_subset_right
  have hU : U ⊆ faces 4 := inter_subset_right
  have hTC : T ⊆ C := inter_subset_left
  have hUC : U ⊆ C := inter_subset_left
  have hM : M ⊆ faces 3 := sdiff_subset
  have hMeq : M = missingTriples C := by
    ext a
    simp only [M, T, missingTriples, mem_sdiff, mem_inter]
    tauto
  have hTU : T ∪ U = C := by
    ext a
    simp only [T, U, mem_union, mem_inter, mem_faces]
    constructor
    · rintro (⟨ha, _⟩ | ⟨ha, _⟩) <;> exact ha
    · intro ha
      exact (hband a ha).imp (fun h => ⟨ha, h⟩) (fun h => ⟨ha, h⟩)
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro s hs hu
    have h₃ := mem_faces.mp (hT hs)
    have h₄ := mem_faces.mp (hU hu)
    omega
  have htotal : T.card + U.card = 144 := by
    rw [← card_union_of_disjoint hdisj, hTU, hcard]
  have ht (a : Face) (ha : a ∈ T) : (above U a).card = 3 := by
    rw [← (band_neighbors (s := a) (k := 3) hband).1 (mem_faces.mp (hT ha))]
    exact hcubic a (hTC ha)
  have hu (a : Face) (ha : a ∈ U) : (below T a).card = 3 := by
    rw [← (band_neighbors (s := a) (k := 3) hband).2 (mem_faces.mp (hU ha))]
    exact hcubic a (hUC ha)
  have hsum : (∑ a ∈ T, (above U a).card) = ∑ a ∈ U, (below T a).card :=
    sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T) (t := U) (fun a b : Face => a ⊆ b)
  rw [sum_const_nat ht, sum_const_nat hu] at hsum
  have hTc : T.card = 72 := by omega
  have hUc : U.card = 72 := by omega
  have hMc : M.card = 12 := by
    change (faces 3 \ T).card = 12
    rw [card_sdiff_of_subset hT, hTc, card_faces] <;> decide
  have hWc : W.card = 54 := by
    change (faces 4 \ U).card = 54
    rw [card_sdiff_of_subset hU, hUc, card_faces] <;> decide
  have htW (a : Face) (ha : a ∈ T) : (above W a).card = 3 := by
    have hc := mem_faces.mp (hT ha)
    have hall : (above (faces 4) a).card = 6 := by
      rw [card_above_faces (s := a) (k := 4) (by omega), hc] <;> decide
    have he := card_filter_complement hU (a ⊆ ·)
    change (above W a).card + (above U a).card = (above (faces 4) a).card at he
    rw [ht a ha, hall] at he
    omega
  have hWsum : (∑ u ∈ W, (below T u).card) = W.card * 4 := by
    calc
      _ = ∑ a ∈ T, (above W a).card :=
        (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := T) (t := W) (fun a b : Face => a ⊆ b)).symm
      _ = T.card * 3 := sum_const_nat htW
      _ = _ := by rw [hTc, hWc] <;> decide
  have hallFour (u : Face) (hu₄ : u ∈ faces 4) : (below (faces 3) u).card = 4 := by
    rw [below_faces, card_powersetCard, mem_faces.mp hu₄] <;> decide
  have hw (u : Face) (huW : u ∈ W) : (below T u).card = 4 := by
    apply eq_const_of_sum_eq (S := W) (f := fun u => (below T u).card) ?_ hWsum huW
    intro v hv
    rw [← hallFour v (sdiff_subset hv)]
    exact card_le_card (filter_subset_filter _ hT)
  have hfour (u : Face) (hu₄ : u ∈ faces 4) :
      (below M u).card = if u ∈ C then 1 else 0 := by
    have he := card_filter_complement hT (· ⊆ u)
    change (below M u).card + (below T u).card = (below (faces 3) u).card at he
    rw [hallFour u hu₄] at he
    by_cases h : u ∈ C
    · rw [ite_eq_left h]
      rw [hu u (mem_inter.mpr ⟨h, hu₄⟩)] at he
      omega
    · rw [ite_eq_right h]
      have huW : u ∈ W := mem_sdiff.mpr ⟨hu₄, fun huU => h (hUC huU)⟩
      rw [hw u huW] at he
      omega
  have hpair_bound (p : Face) (hp : p ∈ faces 2) : (above M p).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨haM, hpa⟩ := mem_filter.mp ha
    obtain ⟨hbM, hpb⟩ := mem_filter.mp hb
    by_contra hab
    have ha₃ := mem_faces.mp (hM haM)
    have hb₃ := mem_faces.mp (hM hbM)
    have hi := card_le_card (subset_inter hpa hpb)
    have hp₂ := mem_faces.mp hp
    have hunion := card_union_add_card_inter a b
    have hgt : 3 < (a ∪ b).card := by
      by_contra! hle
      have hea : a = a ∪ b := eq_of_subset_of_card_le subset_union_left (by omega)
      have heb : b = a ∪ b := eq_of_subset_of_card_le subset_union_right (by omega)
      exact hab (hea.trans heb.symm)
    have huv : a ∪ b ∈ faces 4 := mem_faces.mpr (by omega)
    have hbound : (below M (a ∪ b)).card ≤ 1 := by
      rw [hfour _ huv]
      split <;> decide
    exact hab (card_le_one.mp hbound a (mem_filter.mpr ⟨haM, subset_union_left⟩)
      b (mem_filter.mpr ⟨hbM, subset_union_right⟩))
  have hpairsum : (∑ p ∈ faces 2, (above M p).card) = (faces 2).card * 1 := by
    calc
      _ = ∑ a ∈ M, (below (faces 2) a).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := faces 2) (t := M) (fun a b : Face => a ⊆ b)
      _ = ∑ _a ∈ M, 3 := by
        apply sum_congr rfl
        intro a ha
        rw [below_faces, card_powersetCard, mem_faces.mp (hM ha)] <;> decide
      _ = _ := by rw [sum_const, smul_eq_mul, hMc, card_faces] <;> decide
  rw [← hMeq]
  exact ⟨hMc, fun p hp => eq_const_of_sum_eq hpair_bound hpairsum hp, hfour⟩

/-- Every five-set contains a block of a Steiner triple system on nine points. -/
private theorem exists_triple_in_five {M : Finset Face} (hM : M ⊆ faces 3)
    (hsteiner : ∀ p ∈ faces 2, (above M p).card = 1)
    {s : Face} (hs : s.card = 5) : ∃ a ∈ M, a ⊆ s := by
  by_contra h
  have hnone (a : Face) (ha : a ∈ M) (has : a ⊆ s) : False := h ⟨a, ha, has⟩
  let F := M.filter fun a => (a ∩ s).card = 2
  let X := (univ : Face) \ s
  have hX : X.card = 4 := by
    change ((univ : Face) \ s).card = 4
    rw [card_sdiff_of_subset (subset_univ _), card_univ, Fintype.card_fin, hs] <;> decide
  have hinter (a : Face) (ha : a ∈ M) : (a ∩ s).card ≤ 2 := by
    have ha₃ := mem_faces.mp (hM ha)
    by_contra! h
    have he : a ∩ s = a := eq_of_subset_of_card_le inter_subset_left (by omega)
    exact hnone a ha (he ▸ inter_subset_right)
  have hF : F.card = 10 := by
    have hmap (a : Face) (ha : a ∈ F) : a ∩ s ∈ s.powersetCard 2 :=
      mem_powersetCard.mpr ⟨inter_subset_right, (mem_filter.mp ha).2⟩
    rw [card_eq_sum_card_fiberwise (f := fun a : Face => a ∩ s)
      (t := s.powersetCard 2) (fun a ha => hmap a ha)]
    calc
      _ = ∑ _p ∈ s.powersetCard 2, 1 := by
        apply sum_congr rfl
        intro p hp
        obtain ⟨hps, hp₂⟩ := mem_powersetCard.mp hp
        have he : (F.filter fun a => a ∩ s = p) = above M p := by
          ext a
          constructor
          · intro ha
            obtain ⟨haF, he⟩ := mem_filter.mp ha
            exact mem_filter.mpr ⟨(mem_filter.mp haF).1, he ▸ inter_subset_left⟩
          · intro ha
            obtain ⟨haM, hpa⟩ := mem_filter.mp ha
            have hsub : p ⊆ a ∩ s := subset_inter hpa hps
            have he : p = a ∩ s :=
              eq_of_subset_of_card_le hsub (by simpa only [hp₂] using hinter a haM)
            exact mem_filter.mpr ⟨mem_filter.mpr ⟨haM, he ▸ hp₂⟩, he.symm⟩
        rw [he, hsteiner p (mem_faces.mpr hp₂)]
      _ = 10 := by rw [sum_const, smul_eq_mul, card_powersetCard, hs] <;> decide
  have hlocal (x : Fin 9) (hx : x ∈ X) : (F.filter (x ∈ ·)).card ≤ 2 := by
    let Fx := F.filter (x ∈ ·)
    have hxs := (mem_sdiff.mp hx).2
    have hd : (Fx : Set Face).PairwiseDisjoint (fun a : Face => a ∩ s) := by
      intro a ha b hb hab
      change a ∈ Fx at ha
      change b ∈ Fx at hb
      obtain ⟨haF, hxa⟩ := mem_filter.mp ha
      obtain ⟨hbF, hxb⟩ := mem_filter.mp hb
      change Disjoint (a ∩ s) (b ∩ s)
      rw [Finset.disjoint_left]
      intro y hya hyb
      obtain ⟨hya, hys⟩ := mem_inter.mp hya
      have hyb := (mem_inter.mp hyb).1
      have hxy : x ≠ y := fun h => hxs (h.symm ▸ hys)
      let p : Face := {x, y}
      have hp : p ∈ faces 2 := mem_faces.mpr (card_pair hxy)
      have ha : a ∈ above M p :=
        mem_filter.mpr ⟨(mem_filter.mp haF).1, by simp [p, insert_subset_iff, hxa, hya]⟩
      have hb : b ∈ above M p :=
        mem_filter.mpr ⟨(mem_filter.mp hbF).1, by simp [p, insert_subset_iff, hxb, hyb]⟩
      have hle : (above M p).card ≤ 1 := (hsteiner p hp).le
      exact hab (card_le_one.mp hle a ha b hb)
    have hsub : (Fx.biUnion fun a => a ∩ s) ⊆ s := by
      intro y hy
      obtain ⟨a, _, hya⟩ := mem_biUnion.mp hy
      exact inter_subset_right hya
    have hcount : (Fx.biUnion fun a => a ∩ s).card = Fx.card * 2 := by
      rw [card_biUnion hd]
      calc
        _ = ∑ _a ∈ Fx, 2 := sum_congr rfl fun a ha =>
          (mem_filter.mp (mem_filter.mp ha).1).2
        _ = _ := by simp
    have hle := card_le_card hsub
    rw [hcount, hs] at hle
    exact (show Fx.card ≤ 2 by omega)
  have hthird (a : Face) (ha : a ∈ F) : (X.filter (· ∈ a)).card = 1 := by
    have he : X.filter (· ∈ a) = a \ s := by
      ext x
      simp only [X, mem_filter, mem_sdiff, mem_univ, true_and]
      tauto
    obtain ⟨haM, ha₂⟩ := mem_filter.mp ha
    have h := card_inter_add_card_sdiff a s
    rw [mem_faces.mp (hM haM), ha₂] at h
    rw [he]
    omega
  have hcount : F.card ≤ X.card * 2 := by
    calc
      _ = ∑ a ∈ F, (X.filter (· ∈ a)).card := by
        rw [sum_congr rfl hthird]
        simp
      _ = ∑ x ∈ X, (F.filter (x ∈ ·)).card :=
        sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
          (s := F) (t := X) (fun a x => x ∈ a)
      _ ≤ ∑ _x ∈ X, 2 := sum_le_sum hlocal
      _ = _ := by simp
  omega

/-- The layers outside the closed neighborhood of a cubic 144-point band. -/
def residual : Finset Face := (univ : Face).powerset.filter fun s => s.card ≤ 1 ∨ 6 ≤ s.card

@[simp] theorem mem_residual {s : Face} : s ∈ residual ↔ s.card ≤ 1 ∨ 6 ≤ s.card := by
  simp [residual]

private theorem exists_insert_of_card_lt {a s : Face} (has : a ⊆ s)
    (h : a.card < s.card) : ∃ u, a ⊆ u ∧ u ⊆ s ∧ u.card = a.card + 1 := by
  obtain ⟨x, hxs, hxa⟩ := exists_mem_notMem_of_card_lt_card h
  exact ⟨insert x a, subset_insert _ _, insert_subset_iff.mpr ⟨hxs, has⟩,
    card_insert_of_notMem hxa⟩

/-- The complement of the closed neighborhood is exactly layers 0, 1 and 6–9. -/
theorem mem_residual_iff {C : Finset Face} (hcard : C.card = 144)
    (hband : ∀ s ∈ C, s.card = 3 ∨ s.card = 4)
    (hcubic : ∀ s ∈ C, (neighbors C s).card = 3) (s : Face) :
    s ∈ residual ↔ s ∉ C ∧ ∀ t ∈ C, ¬ Adj s t := by
  obtain ⟨_, hpairs, hfours⟩ := missing_triples_steiner hcard hband hcubic
  let M := missingTriples C
  let T := C ∩ faces 3
  have hT : T ⊆ faces 3 := inter_subset_right
  have hM : M ⊆ faces 3 := sdiff_subset
  have hpart : M = faces 3 \ T := by
    ext a
    simp only [M, missingTriples, T, mem_sdiff, mem_inter]
    tauto
  have hfour_selected (a u : Face) (ha : a ∈ M) (hau : a ⊆ u) (hu : u.card = 4) :
      u ∈ C := by
    by_contra hn
    have hz := hfours u (mem_faces.mpr hu)
    rw [ite_eq_right hn] at hz
    change (below M u).card = 0 at hz
    have hpos : 0 < (below M u).card := card_pos.mpr ⟨a, mem_filter.mpr ⟨ha, hau⟩⟩
    omega
  rw [mem_residual]
  constructor
  · intro hs
    refine ⟨fun h => ?_, fun t ht hadj => ?_⟩
    · rcases hs with hs | hs <;> rcases hband s h with h | h <;> omega
    · rcases hs with hs | hs <;> rcases hband t ht with ht | ht <;>
        rcases hadj with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  · rintro ⟨hsC, hno⟩
    by_contra! hout
    have hcases : s.card = 2 ∨ s.card = 3 ∨ s.card = 4 ∨ s.card = 5 := by omega
    rcases hcases with hs | hs | hs | hs
    · have hall : (above (faces 3) s).card = 7 := by
        rw [card_above_faces (s := s) (k := 3) (by omega), hs] <;> decide
      have hcount := card_filter_complement hT (s ⊆ ·)
      change (above (faces 3 \ T) s).card + (above T s).card = _ at hcount
      rw [← hpart, hpairs s (mem_faces.mpr hs), hall] at hcount
      have hpos : 0 < (above T s).card := by omega
      obtain ⟨t, ht⟩ := card_pos.mp hpos
      obtain ⟨ht, hst⟩ := mem_filter.mp ht
      obtain ⟨htC, ht₃⟩ := mem_inter.mp ht
      have htcard := mem_faces.mp ht₃
      exact hno t htC (Or.inl ⟨hst, by omega⟩)
    · have hsM : s ∈ M := mem_sdiff.mpr ⟨mem_faces.mpr hs, hsC⟩
      have hlt : s.card < (univ : Face).card := by simp [hs]
      obtain ⟨u, hsu, _, hu⟩ := exists_insert_of_card_lt (subset_univ s) hlt
      exact hno u (hfour_selected s u hsM hsu (by omega)) (Or.inl ⟨hsu, hu.symm⟩)
    · have hall : (below (faces 3) s).card = 4 := by
        rw [below_faces, card_powersetCard, hs] <;> decide
      have hz := hfours s (mem_faces.mpr hs)
      rw [ite_eq_right hsC] at hz
      have hcount := card_filter_complement hT (· ⊆ s)
      change (below (faces 3 \ T) s).card + (below T s).card = _ at hcount
      rw [← hpart, hz, hall] at hcount
      have hpos : 0 < (below T s).card := by omega
      obtain ⟨t, ht⟩ := card_pos.mp hpos
      obtain ⟨ht, hts⟩ := mem_filter.mp ht
      obtain ⟨htC, ht₃⟩ := mem_inter.mp ht
      have htcard := mem_faces.mp ht₃
      exact hno t htC (Or.inr ⟨hts, by omega⟩)
    · obtain ⟨a, ha, has⟩ := exists_triple_in_five hM hpairs hs
      have ha₃ := mem_faces.mp (hM ha)
      obtain ⟨u, hau, hus, hu⟩ := exists_insert_of_card_lt has (by omega)
      exact hno u (hfour_selected a u ha hau (by omega)) (Or.inr ⟨hus, by omega⟩)

private theorem residual_card : residual.card = 140 := by
  have hmap (s : Face) (_ : s ∈ residual) : s.card ∈ range 10 := by
    have h := card_le_card (subset_univ s)
    simp only [card_univ, Fintype.card_fin] at h
    exact mem_range.mpr (by omega)
  rw [card_eq_sum_card_fiberwise (f := fun s : Face => s.card) (t := range 10) hmap]
  calc
    _ = ∑ k ∈ range 10, if k ≤ 1 ∨ 6 ≤ k then Nat.choose 9 k else 0 := by
      apply sum_congr rfl
      intro k _
      have he : (residual.filter fun s => s.card = k) =
          if k ≤ 1 ∨ 6 ≤ k then faces k else ∅ := by
        by_cases hk : k ≤ 1 ∨ 6 ≤ k
        · ext s
          simp only [ite_eq_left hk, mem_filter, mem_residual, mem_faces]
          exact ⟨And.right, fun hs => ⟨hs.symm ▸ hk, hs⟩⟩
        · ext s
          simp only [ite_eq_right hk, mem_filter, mem_residual, notMem_empty, iff_false]
          rintro ⟨hs, he⟩
          exact hk (he ▸ hs)
      rw [he]
      split
      · exact card_faces k
      · rfl
    _ = 140 := by decide

private theorem layer_six_seven_deletions {A : Finset Face}
    (hsubcubic : ∀ s ∈ A, (neighbors A s).card ≤ 3) :
    108 + (faces 7 ∩ A).card ≤ 3 * ((faces 6 \ A).card + (faces 7 \ A).card) := by
  let K := faces 7 ∩ A
  let D6 := faces 6 \ A
  let r (s t : Face) := t ⊆ s
  have hleft (s : Face) (hs : s ∈ K) : 4 ≤ (D6.bipartiteAbove r s).card := by
    obtain ⟨hs7, hsA⟩ := mem_inter.mp hs
    have hsCard := mem_faces.mp hs7
    have hall : (below (faces 6) s).card = 7 := by
      rw [below_faces, card_powersetCard, hsCard] <;> decide
    have hretained : (below (faces 6 ∩ A) s).card ≤ 3 := by
      refine (card_le_card ?_).trans (hsubcubic s hsA)
      intro t ht
      obtain ⟨ht, hts⟩ := mem_filter.mp ht
      obtain ⟨ht6, htA⟩ := mem_inter.mp ht
      have htCard := mem_faces.mp ht6
      exact mem_filter.mpr ⟨htA, Or.inr ⟨hts, by omega⟩⟩
    have hsplit := card_filter_complement
      (inter_subset_left : faces 6 ∩ A ⊆ faces 6) (· ⊆ s)
    rw [sdiff_inter_self_left] at hsplit
    change (D6.bipartiteAbove r s).card + (below (faces 6 ∩ A) s).card =
      (below (faces 6) s).card at hsplit
    omega
  have hright (t : Face) (ht : t ∈ D6) : (K.bipartiteBelow r t).card ≤ 3 := by
    have htCard := mem_faces.mp (mem_sdiff.mp ht).1
    have hall : (above (faces 7) t).card = 3 := by
      rw [card_above_faces (s := t) (k := 7) (by omega), htCard] <;> decide
    change (above K t).card ≤ 3
    rw [← hall]
    exact card_le_card (filter_subset_filter _ (inter_subset_left : K ⊆ faces 7))
  -- Each retained site needs four deletions, and each deleted site serves at most three.
  have hcount : K.card * 4 ≤ D6.card * 3 := by
    simpa only [smul_eq_mul] using
      (card_nsmul_le_card_nsmul (s := K) (t := D6) (m := (4 : ℕ)) (n := (3 : ℕ))
        r hleft hright)
  have hcard7 : (faces 7).card = 36 := by rw [card_faces] <;> decide
  have hpart := card_inter_add_card_sdiff (faces 7) A
  rw [hcard7] at hpart
  change K.card + (faces 7 \ A).card = 36 at hpart
  -- At least 36 deletions, with strict inequality whenever a layer-7 site is retained.
  change 108 + K.card ≤ 3 * (D6.card + (faces 7 \ A).card)
  omega

private theorem star_deletions {A L : Finset Face} {c : Face}
    (hL : L.card = 9) (hAdj : ∀ t ∈ L, Adj c t)
    (hsubcubic : ∀ s ∈ A, (neighbors A s).card ≤ 3) :
    1 ≤ ((insert c L) \ A).card ∧ (c ∈ A → 6 ≤ ((insert c L) \ A).card) := by
  have hcenter (hc : c ∈ A) : 6 ≤ ((insert c L) \ A).card := by
    have hretained : (L ∩ A).card ≤ 3 := by
      refine (card_le_card ?_).trans (hsubcubic c hc)
      intro t ht
      obtain ⟨htL, htA⟩ := mem_inter.mp ht
      exact mem_filter.mpr ⟨htA, hAdj t htL⟩
    have hpart := card_inter_add_card_sdiff L A
    have hmissing := card_le_card
      (sdiff_subset_sdiff_left (u := A) (subset_insert c L))
    omega
  refine ⟨?_, hcenter⟩
  by_cases hc : c ∈ A
  · exact le_trans (by decide : 1 ≤ 6) (hcenter hc)
  · exact card_pos.mpr ⟨c, mem_sdiff.mpr ⟨mem_insert_self _ _, hc⟩⟩

private def extremalResidual : Finset Face := faces 1 ∪ faces 6 ∪ faces 8

private theorem mem_extremalResidual {s : Face} :
    s ∈ extremalResidual ↔ s.card = 1 ∨ s.card = 6 ∨ s.card = 8 := by
  simp only [extremalResidual, mem_union, mem_faces, or_assoc]

private theorem extremalResidual_card : extremalResidual.card = 102 := by
  have h16 : Disjoint (faces 1) (faces 6) := by
    apply Finset.disjoint_left.mpr
    intro s h1 h6
    simp only [mem_faces] at h1 h6
    omega
  have h168 : Disjoint (faces 1 ∪ faces 6) (faces 8) := by
    apply Finset.disjoint_left.mpr
    intro s hs h8
    simp only [mem_union, mem_faces] at hs h8
    omega
  rw [extremalResidual, card_union_of_disjoint h168, card_union_of_disjoint h16,
    card_faces, card_faces, card_faces] <;> decide

private theorem residual_deletions_ge {A : Finset Face} (hA : A ⊆ residual)
    (hsubcubic : ∀ s ∈ A, (neighbors A s).card ≤ 3) :
    38 ≤ (residual \ A).card ∧
      ((residual \ A).card = 38 → A = extremalResidual) := by
  let D0 := insert (∅ : Face) (faces 1) \ A
  let D6 := faces 6 \ A
  let D7 := faces 7 \ A
  let D9 := insert (univ : Face) (faces 8) \ A
  have h1 : (faces 1).card = 9 := by rw [card_faces] <;> decide
  have h8 : (faces 8).card = 9 := by rw [card_faces] <;> decide
  have hlow (t : Face) (ht : t ∈ faces 1) : Adj ∅ t :=
    Or.inl ⟨empty_subset t, by simpa only [card_empty, Nat.zero_add] using (mem_faces.mp ht).symm⟩
  have hhigh (t : Face) (ht : t ∈ faces 8) : Adj univ t :=
    Or.inr ⟨subset_univ t, by simp [mem_faces.mp ht]⟩
  obtain ⟨hd0, hcenter0⟩ := star_deletions h1 hlow hsubcubic
  obtain ⟨hd9, hcenter9⟩ := star_deletions h8 hhigh hsubcubic
  change 1 ≤ D0.card at hd0
  change 1 ≤ D9.card at hd9
  change (∅ : Face) ∈ A → 6 ≤ D0.card at hcenter0
  change (univ : Face) ∈ A → 6 ≤ D9.card at hcenter9
  have hmiddle := layer_six_seven_deletions hsubcubic
  change 108 + (faces 7 ∩ A).card ≤ 3 * (D6.card + D7.card) at hmiddle
  have hD0 {s : Face} (hs : s ∈ D0) : s.card ≤ 1 := by
    rcases mem_insert.mp (mem_sdiff.mp hs).1 with rfl | hs
    · simp
    · have := mem_faces.mp hs
      omega
  have hD6 {s : Face} (hs : s ∈ D6) : s.card = 6 := mem_faces.mp (mem_sdiff.mp hs).1
  have hD7 {s : Face} (hs : s ∈ D7) : s.card = 7 := mem_faces.mp (mem_sdiff.mp hs).1
  have hD9 {s : Face} (hs : s ∈ D9) : 8 ≤ s.card := by
    rcases mem_insert.mp (mem_sdiff.mp hs).1 with rfl | hs
    · simp
    · exact le_of_eq (mem_faces.mp hs).symm
  have hD67 {s : Face} (hs : s ∈ D6 ∪ D7) : 6 ≤ s.card ∧ s.card ≤ 7 := by
    rcases mem_union.mp hs with hs | hs
    · rw [hD6 hs] <;> decide
    · rw [hD7 hs] <;> decide
  have hdisj67 : Disjoint D6 D7 := by
    refine Finset.disjoint_left.mpr fun s hs ht => ?_
    have := hD6 hs
    have := hD7 ht
    omega
  have hdisj0 : Disjoint D0 (D6 ∪ D7) := by
    refine Finset.disjoint_left.mpr fun s hs ht => ?_
    have := hD0 hs
    have := (hD67 ht).1
    omega
  have hdisj9 : Disjoint (D0 ∪ (D6 ∪ D7)) D9 := by
    refine Finset.disjoint_left.mpr fun s hs ht => ?_
    have := hD9 ht
    rcases mem_union.mp hs with hs | hs
    · have := hD0 hs
      omega
    · have := (hD67 hs).2
      omega
  have hpieces : D0 ∪ (D6 ∪ D7) ∪ D9 ⊆ residual \ A := by
    intro s hs
    simp only [mem_union] at hs
    rcases hs with (hs | (hs | hs)) | hs
    · exact mem_sdiff.mpr ⟨mem_residual.mpr (Or.inl (hD0 hs)), (mem_sdiff.mp hs).2⟩
    · exact mem_sdiff.mpr
        ⟨mem_residual.mpr (Or.inr (le_of_eq (hD6 hs).symm)), (mem_sdiff.mp hs).2⟩
    · exact mem_sdiff.mpr
        ⟨mem_residual.mpr (Or.inr ((by decide : 6 ≤ 7).trans (le_of_eq (hD7 hs).symm))),
          (mem_sdiff.mp hs).2⟩
    · exact mem_sdiff.mpr
        ⟨mem_residual.mpr (Or.inr ((by decide : 6 ≤ 8).trans (hD9 hs))), (mem_sdiff.mp hs).2⟩
  have htotal := card_le_card hpieces
  rw [card_union_of_disjoint hdisj9, card_union_of_disjoint hdisj0,
    card_union_of_disjoint hdisj67] at htotal
  refine ⟨by omega, fun heq => ?_⟩
  have h0 : (∅ : Face) ∉ A := by
    intro h
    have := hcenter0 h
    omega
  have h9 : (univ : Face) ∉ A := by
    intro h
    have := hcenter9 h
    omega
  have h7 : faces 7 ∩ A = ∅ := card_eq_zero.mp (by omega)
  have hcardA := card_sdiff_add_card_eq_card hA
  rw [residual_card, heq] at hcardA
  apply eq_of_subset_of_card_le _ (by rw [extremalResidual_card]; omega)
  intro s hs
  have hres := mem_residual.mp (hA hs)
  have hle : s.card ≤ 9 := by simpa only [Fintype.card_fin] using s.card_le_univ
  have hs0 : s.card ≠ 0 := fun he => h0 (card_eq_zero.mp he ▸ hs)
  have hs9 : s.card ≠ 9 := by
    intro he
    apply h9
    have hsu := (card_eq_iff_eq_univ s).mp (by simpa only [Fintype.card_fin] using he)
    exact hsu ▸ hs
  have hs7 : s.card ≠ 7 := by
    intro he
    have ht : s ∈ faces 7 ∩ A := mem_inter.mpr ⟨mem_faces.mpr he, hs⟩
    rw [h7] at ht
    exact notMem_empty _ ht
  apply mem_extremalResidual.mpr
  omega

private theorem extension_bound_subset {C A : Finset Face} (hcard : C.card = 144)
    (hband : ∀ s ∈ C, s.card = 3 ∨ s.card = 4)
    (hcubic : ∀ s ∈ C, (neighbors C s).card = 3)
    (hCA : C ⊆ A) (hsubcubic : ∀ s ∈ A, (neighbors A s).card ≤ 3) :
    A.card ≤ 246 ∧ (A.card = 246 → A = C ∪ extremalResidual) := by
  let B := A \ C
  have hB : B ⊆ residual := by
    intro t ht
    obtain ⟨htA, htC⟩ := mem_sdiff.mp ht
    apply (mem_residual_iff hcard hband hcubic t).mpr
    refine ⟨htC, fun s hs hts => ?_⟩
    have hsplit := card_filter_complement hCA (Adj s)
    change (neighbors B s).card + (neighbors C s).card = (neighbors A s).card at hsplit
    have h₃ := hcubic s hs
    have hle := hsubcubic s (hCA hs)
    have hpos : 0 < (neighbors B s).card :=
      card_pos.mpr ⟨t, mem_filter.mpr ⟨ht, adj_comm.mp hts⟩⟩
    omega
  have hBsub (s : Face) (hs : s ∈ B) : (neighbors B s).card ≤ 3 :=
    (card_le_card (filter_subset_filter _ (sdiff_subset : B ⊆ A))).trans
      (hsubcubic s (sdiff_subset hs))
  obtain ⟨hdel, hunique⟩ := residual_deletions_ge hB hBsub
  have hpool := card_sdiff_add_card_eq_card hB
  have htotal := card_sdiff_add_card_eq_card hCA
  change B.card + C.card = A.card at htotal
  rw [residual_card] at hpool
  refine ⟨by omega, fun heq => ?_⟩
  have hB_eq := hunique (by omega)
  calc
    A = C ∪ B := (union_sdiff_of_subset hCA).symm
    _ = C ∪ extremalResidual := by rw [hB_eq]

/-- Every induced subcubic extension of a cubic 144-point band in the subset cube
has at most 246 vertices. -/
private theorem extension_card_le_subset {C A : Finset Face} (hcard : C.card = 144)
    (hband : ∀ s ∈ C, s.card = 3 ∨ s.card = 4)
    (hcubic : ∀ s ∈ C, (neighbors C s).card = 3)
    (hCA : C ⊆ A) (hsubcubic : ∀ s ∈ A, (neighbors A s).card ≤ 3) :
    A.card ≤ 246 :=
  (extension_bound_subset hcard hband hcubic hCA hsubcubic).1

private theorem extremal_extension_subset {C : Finset Face} (hcard : C.card = 144)
    (hband : ∀ s ∈ C, s.card = 3 ∨ s.card = 4)
    (hcubic : ∀ s ∈ C, (neighbors C s).card = 3) :
    (C ∪ extremalResidual).card = 246 ∧
      ∀ s ∈ C ∪ extremalResidual, (neighbors (C ∪ extremalResidual) s).card ≤ 3 := by
  have hres {s : Face} (hs : s ∈ extremalResidual) : s ∉ C ∧ ∀ t ∈ C, ¬ Adj s t :=
    (mem_residual_iff hcard hband hcubic s).mp (mem_residual.mpr (by
      have := mem_extremalResidual.mp hs
      omega))
  have hdisj : Disjoint C extremalResidual :=
    Finset.disjoint_left.mpr fun _ ht hs => (hres hs).1 ht
  refine ⟨?_, ?_⟩
  · rw [card_union_of_disjoint hdisj, hcard, extremalResidual_card]
  · intro s hs
    rcases mem_union.mp hs with hs | hs
    · have he : neighbors (C ∪ extremalResidual) s = neighbors C s := by
        ext t
        simp only [mem_filter, mem_union]
        constructor
        · rintro ⟨ht | ht, hadj⟩
          · exact ⟨ht, hadj⟩
          · exact ((hres ht).2 s hs (adj_comm.mp hadj)).elim
        · rintro ⟨ht, hadj⟩
          exact ⟨Or.inl ht, hadj⟩
      rw [he, hcubic s hs]
    · have he : neighbors (C ∪ extremalResidual) s = ∅ := by
        apply filter_eq_empty_iff.mpr
        intro t ht hadj
        rcases mem_union.mp ht with ht | ht
        · exact (hres hs).2 t ht hadj
        · have := mem_extremalResidual.mp hs
          have := mem_extremalResidual.mp ht
          rcases hadj with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
      rw [he, card_empty] <;> decide

section BooleanCube

open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q)
open SupportedEigenSaturation (selected_neighbor_card)

private def coordinates (x : Q 9) : Face := univ.filter fun i => x i = true
private def point (s : Face) : Q 9 := fun i => decide (i ∈ s)

private theorem point_coordinates (x : Q 9) : point (coordinates x) = x := by
  funext i
  cases h : x i <;> simp [point, coordinates, h]

private theorem coordinates_point (s : Face) : coordinates (point s) = s := by
  ext i
  simp [coordinates, point]

private theorem coordinates_card (x : Q 9) : (coordinates x).card = booleanWeight x := by
  rfl

open private face_adj_iff from
  D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LevelThreeFourObstruction

private theorem point_adj_iff (s t : Face) :
    (hypercube 9).Adj (point s) (point t) ↔ Adj s t :=
  face_adj_iff s t

private theorem mem_image_coordinates {U : Finset (Q 9)} {s : Face} :
    s ∈ U.image coordinates ↔ point s ∈ U := by
  constructor
  · intro hs
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    simpa only [point_coordinates] using hx
  · intro hs
    exact mem_image.mpr ⟨point s, hs, coordinates_point s⟩

open scoped Classical in
private theorem degree_image_coordinates {U : Finset (Q 9)} {s : Face} (hs : point s ∈ U) :
    (neighbors (U.image coordinates) s).card =
      ((hypercube 9).induce (U : Set (Q 9))).degree ⟨point s, hs⟩ := by
  rw [← selected_neighbor_card hs]
  apply card_bij (fun t _ => point t)
  · intro t ht
    obtain ⟨htU, hadj⟩ := mem_filter.mp ht
    exact mem_inter.mpr
      ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr ((point_adj_iff s t).mpr hadj),
        mem_image_coordinates.mp htU⟩
  · intro t _ u _ he
    exact (Function.LeftInverse.injective coordinates_point) he
  · intro x hx
    obtain ⟨hadj, hxU⟩ := mem_inter.mp hx
    refine ⟨coordinates x, mem_filter.mpr ⟨mem_image_of_mem coordinates hxU, ?_⟩,
      point_coordinates x⟩
    apply (point_adj_iff s (coordinates x)).mp
    simpa only [point_coordinates] using ((SimpleGraph.mem_neighborFinset _ _ _).mp hadj)

private theorem coordinates_injective : Function.Injective coordinates :=
  Function.LeftInverse.injective point_coordinates

open scoped Classical in
private theorem degree_le_image_coordinates (U : Finset (Q 9)) :
    (∀ s ∈ U.image coordinates, (neighbors (U.image coordinates) s).card ≤ 3) ↔
      (∀ x : (U : Set (Q 9)), ((hypercube 9).induce (U : Set (Q 9))).degree x ≤ 3) := by
  constructor
  · intro h
    rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ : ∃ s : Face, point s = x := ⟨coordinates x, point_coordinates x⟩
    rw [← degree_image_coordinates (s := s) hx]
    exact h s (mem_image_coordinates.mpr hx)
  · intro h s hs
    rw [degree_image_coordinates (mem_image_coordinates.mp hs)]
    exact h _

open scoped Classical in
private theorem cubic_band_image_coordinates {C : Finset (Q 9)} (hcard : C.card = 144)
    (hband : ∀ x ∈ C, booleanWeight x = 3 ∨ booleanWeight x = 4)
    (hcubic : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    (C.image coordinates).card = 144 ∧
      (∀ s ∈ C.image coordinates, s.card = 3 ∨ s.card = 4) ∧
      ∀ s ∈ C.image coordinates, (neighbors (C.image coordinates) s).card = 3 := by
  refine ⟨by rwa [card_image_of_injective C coordinates_injective], ?_, ?_⟩
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    simpa only [coordinates_card] using hband x hx
  · intro s hs
    rw [degree_image_coordinates (mem_image_coordinates.mp hs)]
    exact hcubic.degree_eq _

open scoped Classical in
/-- Every induced subcubic extension of an induced cubic support of order 144
on Boolean layers 3 and 4 of Q9 has at most 246 vertices. -/
theorem extension_card_le {C A : Finset (Q 9)} (hcard : C.card = 144)
    (hband : ∀ x ∈ C, booleanWeight x = 3 ∨ booleanWeight x = 4)
    (hcubic : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hCA : C ⊆ A)
    (hsubcubic : ∀ x : (A : Set (Q 9)), ((hypercube 9).induce (A : Set (Q 9))).degree x ≤ 3) :
    A.card ≤ 246 := by
  obtain ⟨hcard', hband', hcubic'⟩ := cubic_band_image_coordinates hcard hband hcubic
  have h := extension_card_le_subset hcard' hband' hcubic' (image_subset_image hCA)
    ((degree_le_image_coordinates A).mpr hsubcubic)
  simpa only [card_image_of_injective A coordinates_injective] using h

open scoped Classical in
private theorem image_layer_extension (C : Finset (Q 9)) :
    (C ∪ univ.filter (fun x => booleanWeight x = 1 ∨ booleanWeight x = 6 ∨
        booleanWeight x = 8)).image coordinates = C.image coordinates ∪ extremalResidual := by
  ext s
  have hw : booleanWeight (point s) = s.card := by
    rw [← coordinates_card, coordinates_point]
  simp only [mem_image_coordinates, mem_union, mem_filter, mem_univ, true_and,
    mem_extremalResidual, hw]

open scoped Classical in
/-- The unique maximum induced subcubic extension is obtained by adjoining all
Boolean vertices of weights 1, 6 and 8. -/
theorem extension_card_eq_iff {C A : Finset (Q 9)} (hcard : C.card = 144)
    (hband : ∀ x ∈ C, booleanWeight x = 3 ∨ booleanWeight x = 4)
    (hcubic : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3) :
    (C ⊆ A ∧
      (∀ x : (A : Set (Q 9)), ((hypercube 9).induce (A : Set (Q 9))).degree x ≤ 3) ∧
      A.card = 246) ↔
      A = C ∪ univ.filter (fun x => booleanWeight x = 1 ∨ booleanWeight x = 6 ∨
        booleanWeight x = 8) := by
  obtain ⟨hcard', hband', hcubic'⟩ := cubic_band_image_coordinates hcard hband hcubic
  constructor
  · rintro ⟨hCA, hsubcubic, heq⟩
    have h := extension_bound_subset hcard' hband' hcubic' (image_subset_image hCA)
      ((degree_le_image_coordinates A).mpr hsubcubic)
    apply Finset.image_injective coordinates_injective
    rw [image_layer_extension]
    exact h.2 (by rwa [card_image_of_injective A coordinates_injective])
  · rintro rfl
    obtain ⟨hcardA, hdegA⟩ := extremal_extension_subset hcard' hband' hcubic'
    refine ⟨subset_union_left, (degree_le_image_coordinates _).mp ?_, ?_⟩
    · rwa [image_layer_extension]
    · rw [← card_image_of_injective _ coordinates_injective, image_layer_extension]
      exact hcardA

end BooleanCube

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9SteinerLayerExtension
