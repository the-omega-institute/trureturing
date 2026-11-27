/- GID: D5/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/HypercubeCritical/ComponentBoundary/Q9LevelThreeFourObstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Data.Finset.Powerset, mathlib/module/Mathlib.Combinatorics.Enumerative.DoubleCounting, mathlib/module/Mathlib.Algebra.BigOperators.ModEq]
   utility: none
   digest: Missing triple incidences exclude a cubic support on levels three and four. -/

import D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Finset.Powerset

/-! Ordered pairs of missing triples count the same incidences by union and by intersection. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LevelThreeFourObstruction

open Finset
open scoped BigOperators

private abbrev Face := Finset (Fin 9)
private abbrev faces (k : ℕ) : Finset Face := (univ : Face).powersetCard k

private theorem mem_faces {s : Face} {k : ℕ} : s ∈ faces k ↔ s.card = k := by
  simp [faces]

private theorem four_degree_sum {M : Finset Face} (hM : M ⊆ faces 3) :
    (∑ u ∈ faces 4, (M.filter (· ⊆ u)).card) = 6 * M.card := by
  calc
    _ = ∑ a ∈ M, ((faces 4).filter (a ⊆ ·)).card :=
      (sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := M) (t := faces 4) (· ⊆ ·)).symm
    _ = ∑ _a ∈ M, 6 := by
      apply sum_congr rfl
      intro a ha
      have hc := mem_faces.mp (hM ha)
      rw [faces, card_filter_powersetCard_subset a univ 4 (subset_univ _) (by omega), hc]
      decide
    _ = _ := by simp [mul_comm]

private theorem pair_degree_sum {M : Finset Face} (hM : M ⊆ faces 3) :
    (∑ p ∈ faces 2, (M.filter (p ⊆ ·)).card) = 3 * M.card := by
  calc
    _ = ∑ a ∈ M, ((faces 2).filter (· ⊆ a)).card :=
      sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
        (s := faces 2) (t := M) (· ⊆ ·)
    _ = ∑ _a ∈ M, 3 := by
      apply sum_congr rfl
      intro a ha
      have he : (faces 2).filter (· ⊆ a) = a.powersetCard 2 := by
        ext p
        simp [and_comm]
      rw [he, card_powersetCard, mem_faces.mp (hM ha)]
      decide
    _ = _ := by simp [mul_comm]

private theorem triple_pair_geometry {a b : Face} (ha : a.card = 3) (hb : b.card = 3) :
    (a ∪ b).card = 4 ↔ (a ∩ b).card = 2 := by
  have h := card_union_add_card_inter a b
  omega

private theorem adjacent_triple_count {M : Finset Face} (hM : M ⊆ faces 3) :
    (∑ u ∈ faces 4, (M.filter (· ⊆ u)).offDiag.card) =
      ∑ p ∈ faces 2, (M.filter (p ⊆ ·)).offDiag.card := by
  let A := M.offDiag.filter (fun ab => (ab.1 ∩ ab.2).card = 2)
  have hcards {ab : Face × Face} (hab : ab ∈ M.offDiag) :
      ab.1.card = 3 ∧ ab.2.card = 3 ∧ ab.1 ≠ ab.2 := by
    obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp hab
    exact ⟨mem_faces.mp (hM ha), mem_faces.mp (hM hb), hn⟩
  have hUnion (u : Face) (hu : u ∈ faces 4) :
      A.filter (fun ab => ab.1 ∪ ab.2 = u) = (M.filter (· ⊆ u)).offDiag := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hA, he⟩ := mem_filter.mp hab
      obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp (mem_filter.mp hA).1
      exact mem_offDiag.mpr
        ⟨mem_filter.mpr ⟨ha, he ▸ subset_union_left⟩,
          mem_filter.mpr ⟨hb, he ▸ subset_union_right⟩, hn⟩
    · intro hab
      obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp hab
      obtain ⟨haM, hau⟩ := mem_filter.mp ha
      obtain ⟨hbM, hbu⟩ := mem_filter.mp hb
      have habM : ab ∈ M.offDiag := mem_offDiag.mpr ⟨haM, hbM, hn⟩
      have ⟨hac, hbc, _⟩ := hcards habM
      have hsub : ab.1 ∪ ab.2 ⊆ u := union_subset hau hbu
      have hlt : 3 < (ab.1 ∪ ab.2).card := by
        by_contra! hle
        have haeq : ab.1 = ab.1 ∪ ab.2 :=
          eq_of_subset_of_card_le subset_union_left (hac ▸ hle)
        have hbeq : ab.2 = ab.1 ∪ ab.2 :=
          eq_of_subset_of_card_le subset_union_right (hbc ▸ hle)
        exact hn (haeq.trans hbeq.symm)
      have huc := mem_faces.mp hu
      have hc : (ab.1 ∪ ab.2).card = 4 := by have := card_le_card hsub; omega
      have he := eq_of_subset_of_card_le hsub (by omega)
      exact mem_filter.mpr ⟨mem_filter.mpr
        ⟨habM, (triple_pair_geometry hac hbc).mp hc⟩, he⟩
  have hInter (p : Face) (hp : p ∈ faces 2) :
      A.filter (fun ab => ab.1 ∩ ab.2 = p) = (M.filter (p ⊆ ·)).offDiag := by
    ext ab
    constructor
    · intro hab
      obtain ⟨hA, he⟩ := mem_filter.mp hab
      obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp (mem_filter.mp hA).1
      exact mem_offDiag.mpr
        ⟨mem_filter.mpr ⟨ha, he ▸ inter_subset_left⟩,
          mem_filter.mpr ⟨hb, he ▸ inter_subset_right⟩, hn⟩
    · intro hab
      obtain ⟨ha, hb, hn⟩ := mem_offDiag.mp hab
      obtain ⟨haM, hpa⟩ := mem_filter.mp ha
      obtain ⟨hbM, hpb⟩ := mem_filter.mp hb
      have habM : ab ∈ M.offDiag := mem_offDiag.mpr ⟨haM, hbM, hn⟩
      have ⟨hac, hbc, _⟩ := hcards habM
      have hsub : p ⊆ ab.1 ∩ ab.2 := subset_inter hpa hpb
      have hlt : (ab.1 ∩ ab.2).card < 3 := by
        by_contra! hle
        have haeq : ab.1 ∩ ab.2 = ab.1 :=
          eq_of_subset_of_card_le inter_subset_left (hac ▸ hle)
        have hbeq : ab.1 ∩ ab.2 = ab.2 :=
          eq_of_subset_of_card_le inter_subset_right (hbc ▸ hle)
        exact hn (haeq.symm.trans hbeq)
      have hpc := mem_faces.mp hp
      have hc : (ab.1 ∩ ab.2).card = 2 := by have := card_le_card hsub; omega
      have he := eq_of_subset_of_card_le hsub (by omega)
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨habM, hc⟩, he.symm⟩
  calc
    _ = A.card := by
      rw [card_eq_sum_card_fiberwise
        (f := fun ab : Face × Face => ab.1 ∪ ab.2) (t := faces 4) (s := A) ?_]
      · exact sum_congr rfl fun u hu => congrArg card (hUnion u hu).symm
      · intro ab hab
        obtain ⟨hMab, hi⟩ := mem_filter.mp hab
        obtain ⟨ha, hb, _⟩ := hcards hMab
        exact mem_faces.mpr ((triple_pair_geometry ha hb).mpr hi)
    _ = _ := by
      rw [card_eq_sum_card_fiberwise
        (f := fun ab : Face × Face => ab.1 ∩ ab.2) (t := faces 2) (s := A)
        (fun _ hab => mem_faces.mpr (mem_filter.mp hab).2)]
      exact sum_congr rfl fun p hp => congrArg card (hInter p hp)

private theorem odd_degree_mod_eight (b : ℕ) (hb : Odd b) :
    b * b - b ≡ 6 * (b / 2) [MOD 8] := by
  let t := b / 2
  have hodd := Nat.odd_iff.mp hb
  have h : b = 2 * t + 1 := by dsimp [t]; omega
  have hpoly : b * b = b + (2 * t) * (2 * t + 1) := by rw [h]; ring
  have hd : b * b - b = 4 * (t * (t - 1)) + 6 * t := by
    rw [hpoly, Nat.add_sub_cancel_left]
    cases t with
    | zero => simp
    | succ k => simp; ring
  have he : 2 ∣ t * (t - 1) := by
    by_cases ht : t % 2 = 0
    · exact dvd_mul_of_dvd_left (Nat.dvd_of_mod_eq_zero ht) _
    · exact dvd_mul_of_dvd_right (Nat.dvd_of_mod_eq_zero (by omega)) _
  obtain ⟨j, hj⟩ := he
  rw [hd, hj, Nat.ModEq]
  have hj' : 4 * (2 * j) = 8 * j := by omega
  rw [hj']
  omega

/-- A family of thirty missing triples on nine axes cannot have every pair degree
odd, exactly fifty-four four-sets of degree one, and no four-set of degree three. -/
theorem no_missing_triples (M : Finset (Finset (Fin 9)))
    (hM : M ⊆ (univ : Finset (Fin 9)).powersetCard 3) (hcard : M.card = 30)
    (hodd : ∀ p ∈ (univ : Finset (Fin 9)).powersetCard 2, Odd (M.filter (p ⊆ ·)).card)
    (hone : (((univ : Finset (Fin 9)).powersetCard 4).filter fun u =>
      (M.filter (· ⊆ u)).card = 1).card = 54)
    (hthree : ∀ u ∈ (univ : Finset (Fin 9)).powersetCard 4,
      (M.filter (· ⊆ u)).card ≠ 3) : False := by
  let upper (u : Face) := (M.filter (· ⊆ u)).card
  let lower (p : Face) := (M.filter (p ⊆ ·)).card
  have hupper : (∑ u ∈ faces 4, upper u) = 180 := by
    rw [show (∑ u ∈ faces 4, upper u) = _ from four_degree_sum hM, hcard]
  have hlower : (∑ p ∈ faces 2, lower p) = 90 := by
    rw [show (∑ p ∈ faces 2, lower p) = _ from pair_degree_sum hM, hcard]
  have hpaircard : (faces 2).card = 36 := by
    simp [faces, card_powersetCard, show Nat.choose 9 2 = 36 by decide]
  have ht : (∑ p ∈ faces 2, lower p / 2) = 27 := by
    have he : (∑ p ∈ faces 2, lower p) = ∑ p ∈ faces 2, (2 * (lower p / 2) + 1) := by
      apply sum_congr rfl
      intro p hp
      have h := Nat.odd_iff.mp (hodd p hp)
      change lower p % 2 = 1 at h
      omega
    rw [sum_add_distrib, ← mul_sum, sum_const, smul_eq_mul, hpaircard, hlower] at he
    omega
  have hcount := adjacent_triple_count hM
  simp only [offDiag_card] at hcount
  change (∑ u ∈ faces 4, (upper u * upper u - upper u)) =
      ∑ p ∈ faces 2, (lower p * lower p - lower p) at hcount
  have hl : (∑ p ∈ faces 2, (lower p * lower p - lower p)) ≡ 162 [MOD 8] := by
    have he := Nat.ModEq.sum (s := faces 2) fun p hp => odd_degree_mod_eight (lower p) (hodd p hp)
    rwa [← mul_sum, ht] at he
  have hu : (∑ u ∈ faces 4, (upper u * upper u - upper u)) + 54 ≡ 180 [MOD 8] := by
    have hlocal (u : Face) (hu : u ∈ faces 4) :
        upper u * upper u - upper u + (if upper u = 1 then 1 else 0) ≡ upper u [MOD 8] := by
      have hsub : M.filter (· ⊆ u) ⊆ u.powersetCard 3 := by
        intro a ha
        obtain ⟨haM, hau⟩ := mem_filter.mp ha
        exact mem_powersetCard.mpr ⟨hau, mem_faces.mp (hM haM)⟩
      have hle : upper u ≤ 4 := by
        have h := card_le_card hsub
        rwa [card_powersetCard, mem_faces.mp hu] at h
      have hne : upper u ≠ 3 := hthree u hu
      interval_cases upper u <;> norm_num [Nat.ModEq] at *
    have he := Nat.ModEq.sum (s := faces 4) hlocal
    rw [sum_add_distrib, ← card_filter, hupper] at he
    rwa [show ((faces 4).filter (fun u => upper u = 1)).card = 54 from hone] at he
  rw [hcount] at hu
  exact (by decide : ¬ (162 + 54 ≡ 180 [MOD 8])) ((hl.add_right 54).symm.trans hu)

#print axioms no_missing_triples

open Classical
open D5.S3.Combinatorics.Graph.Hypercube (hypercube)
open BalancedCriticalSpectrum (Q IsBalanced)
open BalancedCubeComponentBoundary (directions directions_card regular_directions exterior_even)
open private trueDirections from
  D5.S3.Combinatorics.Graph.HypercubeCritical.SixtySixPointSupport.WeightLayerParity

private def point (s : Face) : Q 9 := fun i => decide (i ∈ s)

private theorem point_trueDirections (x : Q 9) : point (trueDirections x) = x := by
  funext i
  cases hi : x i <;> simp [point, trueDirections, hi]

private theorem trueDirections_point (s : Face) : trueDirections (point s) = s := by
  ext i
  simp [trueDirections, point]

private abbrev selected (C : Finset (Q 9)) := C.image trueDirections

private theorem card_selected (C : Finset (Q 9)) : (selected C).card = C.card :=
  card_image_of_injective C (Function.LeftInverse.injective point_trueDirections)

private theorem mem_selected_iff (C : Finset (Q 9)) (s : Face) :
    s ∈ selected C ↔ point s ∈ C := by
  constructor
  · rintro hs
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    simpa only [point_trueDirections] using hx
  · intro hs
    exact mem_image.mpr ⟨point s, hs, trueDirections_point s⟩

private theorem face_adj_iff (s t : Face) :
    (hypercube 9).Adj (point s) (point t) ↔
      (s ⊆ t ∧ s.card + 1 = t.card) ∨ (t ⊆ s ∧ t.card + 1 = s.card) := by
  change ((univ : Face).filter (fun i => point s i ≠ point t i)).card = 1 ↔ _
  have he : (univ : Face).filter (fun i => point s i ≠ point t i) = (s \ t) ∪ (t \ s) := by
    ext i
    by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [point, hs, ht]
  have hd : Disjoint (s \ t) (t \ s) := by
    rw [Finset.disjoint_left]
    simp only [mem_sdiff]
    tauto
  rw [he, card_union_of_disjoint hd]
  have hst : (s \ t).card = 0 ↔ s ⊆ t := card_eq_zero.trans sdiff_eq_empty_iff_subset
  have hts : (t \ s).card = 0 ↔ t ⊆ s := card_eq_zero.trans sdiff_eq_empty_iff_subset
  constructor
  · intro h
    by_cases hzero : (s \ t).card = 0
    · have hsub := hst.mp hzero
      rw [card_sdiff_of_subset hsub] at h
      exact Or.inl ⟨hsub, by omega⟩
    · have hsub : t ⊆ s := hts.mp (by omega)
      have hdiff := card_sdiff_of_subset hsub
      exact Or.inr ⟨hsub, by omega⟩
  · rintro (⟨hsub, hc⟩ | ⟨hsub, hc⟩)
    · rw [hst.mpr hsub, card_sdiff_of_subset hsub]
      omega
    · rw [hts.mpr hsub, card_sdiff_of_subset hsub]
      omega

private abbrev layer (A : Finset Face) (k : ℕ) := A.filter (fun s => s.card = k)

private noncomputable def neighbors (A : Finset Face) (s : Face) :=
  A.filter (fun t => (hypercube 9).Adj (point s) (point t))

private theorem neighbors_card (C : Finset (Q 9)) (s : Face) :
    (neighbors (selected C) s).card = (directions C (point s)).card := by
  rw [directions_card]
  apply card_bij (fun t _ => point t)
  · intro t ht
    obtain ⟨ht, ha⟩ := mem_filter.mp ht
    exact mem_filter.mpr ⟨(mem_selected_iff C t).mp ht, ha⟩
  · intro t _ u _ he
    exact (Function.LeftInverse.injective trueDirections_point) he
  · intro x hx
    refine ⟨trueDirections x, ?_, point_trueDirections x⟩
    simpa only [neighbors, mem_filter, mem_selected_iff, point_trueDirections] using
      (mem_filter.mp hx)

private theorem band_neighbors {A : Finset Face} (k : ℕ)
    (hA : ∀ s ∈ A, s.card = k ∨ s.card = k + 1) {s : Face} :
    (s.card = k → neighbors A s = (layer A (k + 1)).filter (s ⊆ ·)) ∧
    (s.card = k + 1 → neighbors A s = (layer A k).filter (· ⊆ s)) := by
  constructor <;> intro hs <;> ext t <;>
    simp only [neighbors, face_adj_iff, layer, mem_filter]
  · constructor
    · rintro ⟨ht, (⟨hst, hc⟩ | ⟨_, hc⟩)⟩
      · exact ⟨⟨ht, by omega⟩, hst⟩
      · rcases hA t ht with h | h <;> omega
    · rintro ⟨⟨ht, hc⟩, hst⟩
      exact ⟨ht, Or.inl ⟨hst, by omega⟩⟩
  · constructor
    · rintro ⟨ht, (⟨_, hc⟩ | ⟨hts, hc⟩)⟩
      · rcases hA t ht with h | h <;> omega
      · exact ⟨⟨ht, by omega⟩, hts⟩
    · rintro ⟨⟨ht, hc⟩, hts⟩
      exact ⟨ht, Or.inr ⟨hts, by omega⟩⟩

private theorem complement_degree {T U : Finset Face} (hTU : T ⊆ U)
    (P : Face → Prop) [DecidablePred P] :
    ((U \ T).filter P).card + (T.filter P).card = (U.filter P).card := by
  have hfilter : (U \ T).filter P = U.filter P \ T.filter P := by
    ext a
    simp only [mem_filter, mem_sdiff]
    tauto
  rw [hfilter, card_sdiff_of_subset (filter_subset_filter _ hTU)]
  have := card_le_card (filter_subset_filter P hTU)
  omega

/-- A Huang-balanced cubic support of size 108 cannot lie in Boolean layers 3 and 4. -/
theorem no_balanced_cubic_support {C : Finset (Q 9)}
    (hcard : C.card = 108)
    (hr : ((hypercube 9).induce (C : Set (Q 9))).IsRegularOfDegree 3)
    (hb : IsBalanced C)
    (hband : ∀ x ∈ C, booleanWeight x = 3 ∨ booleanWeight x = 4) : False := by
  let A := selected C
  let T := layer A 3
  let U := layer A 4
  have hA : ∀ s ∈ A, s.card = 3 ∨ s.card = 3 + 1 := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hs
    exact hband x hx
  have hT : T ⊆ faces 3 := fun _ hs => mem_faces.mpr (mem_filter.mp hs).2
  have hU : U ⊆ faces 4 := fun _ hs => mem_faces.mpr (mem_filter.mp hs).2
  have hreg (s : Face) (hs : s ∈ A) : (neighbors A s).card = 3 :=
    (neighbors_card C s).trans (regular_directions C hr ((mem_selected_iff C s).mp hs))
  have hexterior (s : Face) (hs : s ∉ A) : Even (neighbors A s).card := by
    rw [neighbors_card]
    exact exterior_even C hr hb (point s) (fun h => hs ((mem_selected_iff C s).mpr h))
  have hupper (u : Face) (hu : u ∈ faces 4) :
      neighbors A u = T.filter (· ⊆ u) := (band_neighbors 3 hA).2 (mem_faces.mp hu)
  have hUnion : T ∪ U = A := by
    ext s
    simp only [T, U, layer, mem_union, mem_filter]
    exact ⟨fun h => h.elim And.left And.left, fun h =>
      (hA s h).elim (fun h3 => Or.inl ⟨h, h3⟩) (fun h4 => Or.inr ⟨h, h4⟩)⟩
  have hdisj : Disjoint T U := by
    rw [Finset.disjoint_left]
    intro s hs ht
    have h3 := (mem_filter.mp hs).2
    have h4 := (mem_filter.mp ht).2
    omega
  have htotal : T.card + U.card = 108 := by
    rw [← card_union_of_disjoint hdisj, hUnion, card_selected, hcard]
  have hleft (s : Face) (hs : s ∈ T) : (U.bipartiteAbove (· ⊆ ·) s).card = 3 := by
    change (U.filter (s ⊆ ·)).card = 3
    rw [← (band_neighbors 3 hA).1 (mem_filter.mp hs).2]
    exact hreg s (mem_filter.mp hs).1
  have hright (u : Face) (hu : u ∈ U) : (T.bipartiteBelow (· ⊆ ·) u).card = 3 := by
    change (T.filter (· ⊆ u)).card = 3
    rw [← hupper u (hU hu)]
    exact hreg u (mem_filter.mp hu).1
  have hsum := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (s := T) (t := U) (· ⊆ ·)
  rw [sum_congr rfl hleft, sum_congr rfl hright] at hsum
  simp only [sum_const, smul_eq_mul] at hsum
  have hTc : T.card = 54 := by omega
  have hUc : U.card = 54 := by omega
  let M := faces 3 \ T
  have hMcard : M.card = 30 := by
    change (faces 3 \ T).card = _
    rw [card_sdiff_of_subset hT, hTc]
    decide
  have hodd (p : Face) (hp : p ∈ faces 2) : Odd (M.filter (p ⊆ ·)).card := by
    have hpc := mem_faces.mp hp
    have hpA : p ∉ A := fun ha => by rcases hA p ha with h | h <;> omega
    have hN : neighbors A p = T.filter (p ⊆ ·) := by
      ext s
      simp only [neighbors, T, layer, mem_filter]
      constructor
      · rintro ⟨hs, hadj⟩
        rcases (face_adj_iff p s).mp hadj with ⟨hsub, hc⟩ | ⟨_, hc⟩
        · exact ⟨⟨hs, by omega⟩, hsub⟩
        · rcases hA s hs with h3 | h4 <;> omega
      · rintro ⟨⟨hs, hc⟩, hsub⟩
        exact ⟨hs, (face_adj_iff p s).mpr (Or.inl ⟨hsub, by omega⟩)⟩
    have heven := hexterior p hpA
    rw [hN, Nat.even_iff] at heven
    have hall : ((faces 3).filter (p ⊆ ·)).card = 7 := by
      rw [faces, card_filter_powersetCard_subset p univ 3 (subset_univ _) (by omega), hpc]
      decide
    have hcount := complement_degree hT (p ⊆ ·)
    rw [hall] at hcount
    rw [Nat.odd_iff]
    change ((faces 3 \ T).filter (p ⊆ ·)).card % 2 = 1
    omega
  have hfour (u : Face) (hu : u ∈ faces 4) :
      ((M.filter (· ⊆ u)).card = 1 ↔ u ∈ U) ∧ (M.filter (· ⊆ u)).card ≠ 3 := by
    have hall : ((faces 3).filter (· ⊆ u)).card = 4 := by
      have he : (faces 3).filter (· ⊆ u) = u.powersetCard 3 := by
        ext a
        simp [and_comm]
      rw [he, card_powersetCard, mem_faces.mp hu]
      decide
    have hcount := complement_degree hT (· ⊆ u)
    rw [hall] at hcount
    change (M.filter (· ⊆ u)).card + (T.filter (· ⊆ u)).card = 4 at hcount
    by_cases huA : u ∈ A
    · have huU : u ∈ U := mem_filter.mpr ⟨huA, mem_faces.mp hu⟩
      have hdegree := hreg u huA
      rw [hupper u hu] at hdegree
      simp only [huU, iff_true]
      omega
    · have huU : u ∉ U := fun h => huA (mem_filter.mp h).1
      have heven := hexterior u huA
      rw [hupper u hu, Nat.even_iff] at heven
      simp only [huU, iff_false]
      omega
  have hone : ((faces 4).filter (fun u => (M.filter (· ⊆ u)).card = 1)).card = 54 := by
    have he : (faces 4).filter (fun u => (M.filter (· ⊆ u)).card = 1) = U := by
      ext u
      exact ⟨fun h => by
        obtain ⟨hu, hd⟩ := mem_filter.mp h
        exact (hfour u hu).1.mp hd, fun h => mem_filter.mpr ⟨hU h, (hfour u (hU h)).1.mpr h⟩⟩
    rw [he, hUc]
  exact no_missing_triples M sdiff_subset hMcard hodd hone (fun u hu => (hfour u hu).2)

#print axioms no_balanced_cubic_support

end D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9LevelThreeFourObstruction
