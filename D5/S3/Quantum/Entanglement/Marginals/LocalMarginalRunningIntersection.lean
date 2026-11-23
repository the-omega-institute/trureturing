/- GID: D5/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/Marginals/LocalMarginalRunningIntersection
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Local marginal ranks by adjacent overlap counts. -/

import D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRank

/-! Rank formulas for ordered regional partial traces with running intersection. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection

open LocalMarginalRank

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {K : Type*} [Field K]

/-- A site present in two regions stays present in every region between them. -/
def RunningIntersection {A : Type*} [DecidableEq A] : List (Finset A) → Prop
  | [] | [_] => True
  | x :: y :: tail =>
    (∀ z ∈ tail, x ∩ z ⊆ y) ∧ RunningIntersection (y :: tail)

private def listUnion {A : Type*} [DecidableEq A] : List (Finset A) → Finset A
  | [] => ∅
  | x :: tail => x ∪ listUnion tail

private theorem mem_listUnion {A : Type*} [DecidableEq A] (regions : List (Finset A))
    (i : A) : i ∈ listUnion regions ↔ ∃ s ∈ regions, i ∈ s := by
  induction regions with
  | nil => simp [listUnion]
  | cons s regions ih => simp [listUnion, ih]

private theorem adjacent_intersection {A : Type*} [DecidableEq A]
    (x y : Finset A) (tail : List (Finset A))
    (h : ∀ z ∈ tail, x ∩ z ⊆ y) :
    x ∩ listUnion (y :: tail) = x ∩ y := by
  ext i
  simp only [Finset.mem_inter, listUnion, Finset.mem_union, mem_listUnion]
  constructor
  · rintro ⟨hx, hy | ⟨z, hz, hi⟩⟩
    · exact ⟨hx, hy⟩
    · exact ⟨hx, h z hz (Finset.mem_inter.mpr ⟨hx, hi⟩)⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, Or.inl hy⟩

private theorem card_listUnion_add_overlap {A : Type*} [DecidableEq A] :
    ∀ regions : List (Finset A), RunningIntersection regions →
      (listUnion regions).card + (regions.zipWith (fun s t => (s ∩ t).card) regions.tail).sum =
        (regions.map Finset.card).sum
  | [], _ => by simp [listUnion]
  | [x], _ => by simp [listUnion]
  | x :: y :: tail, h => by
    have ha := Finset.card_union_add_card_inter x (listUnion (y :: tail))
    rw [adjacent_intersection x y tail h.1] at ha
    have hr := card_listUnion_add_overlap (y :: tail) h.2
    simp only [listUnion, List.tail_cons, List.zipWith_cons_cons, List.map_cons, List.sum_cons] at *
    omega

private noncomputable def localPairs (allowed : Finset V → Prop) (s : Finset V) :
    Finset (LegalPair allowed) := by
  classical
  let := Fintype.ofFinite (LegalPair allowed)
  exact Finset.univ.filter fun p => occupied p.1 ⊆ s

private theorem localPairs_inter (allowed : Finset V → Prop) (s t : Finset V) :
    localPairs allowed s ∩ localPairs allowed t = localPairs allowed (s ∩ t) := by
  ext p
  simp [localPairs, Finset.subset_inter_iff]

private theorem localPairs_mono {allowed : Finset V → Prop} {s t : Finset V}
    (h : s ⊆ t) : localPairs allowed s ⊆ localPairs allowed t := by
  intro i hi
  have hu : occupied i.1 ⊆ s := by simpa [localPairs] using hi
  simpa [localPairs] using hu.trans h

private theorem chain_localPairs {allowed : Finset V → Prop} :
    ∀ regions : List (Finset V), RunningIntersection regions →
      RunningIntersection (regions.map (localPairs allowed))
  | [], _ => trivial
  | [_], _ => trivial
  | x :: y :: tail, h => by
    constructor
    · intro region hregion
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hregion
      rw [localPairs_inter]
      exact localPairs_mono (h.1 z hz)
    · exact chain_localPairs (y :: tail) h.2

private theorem count_cover (allowed : Finset V → Prop) (regions : List (Finset V)) :
    (listUnion (regions.map (localPairs allowed))).card =
      Nat.card {p : LegalPair allowed // Covered {s | s ∈ regions} p.1} := by
  let := Fintype.ofFinite (LegalPair allowed)
  have mem (p : LegalPair allowed) : p ∈ listUnion (regions.map (localPairs allowed)) ↔
      Covered {s | s ∈ regions} p.1 := by
    simp only [mem_listUnion, Covered, Set.mem_ofPred_eq, List.mem_map]
    constructor
    · rintro ⟨_, ⟨s, hs, rfl⟩, hp⟩
      exact ⟨s, hs, by simpa [localPairs] using hp⟩
    · rintro ⟨s, hs, hp⟩
      exact ⟨localPairs allowed s, ⟨s, hs, rfl⟩, by simpa [localPairs] using hp⟩
  classical
  let e := Equiv.subtypeEquivRight mem
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]

private theorem localPairs_zipWith (allowed : Finset V → Prop) :
    ∀ regions : List (Finset V),
      ((regions.map (localPairs allowed)).zipWith (fun s t => (s ∩ t).card)
        (regions.map (localPairs allowed)).tail).sum =
      (regions.zipWith (fun s t => (localPairs allowed (s ∩ t)).card) regions.tail).sum
  | [] => by simp
  | [_] => by simp
  | x :: y :: tail => by
    simp only [List.map_cons, List.tail_cons, List.zipWith_cons_cons, List.sum_cons,
      localPairs_inter]
    have rest := localPairs_zipWith allowed (y :: tail)
    simpa only [List.map_cons, List.tail_cons] using
      congrArg ((localPairs allowed (x ∩ y)).card + ·) rest

/-- The number of ordered legal pairs supported entirely in a region. -/
noncomputable def regionPairCount (allowed : Finset V → Prop) (region : Finset V) : ℕ :=
  (localPairs allowed region).card

/-- For regions with running intersection, the collected rank plus the adjacent overlap counts
equals the sum of individual region counts. -/
theorem finrank_add_adjacentOverlap {allowed : Finset V → Prop}
    (closed : DownwardClosed allowed) (regions : List (Finset V))
    (h : RunningIntersection regions) :
    Module.finrank K (marginalMap (K := K) (allowed := allowed) {s | s ∈ regions}).range +
      (regions.zipWith (fun s t => regionPairCount allowed (s ∩ t)) regions.tail).sum =
      (regions.map (regionPairCount allowed)).sum := by
  rw [finrank_marginalMap closed, ← count_cover allowed regions]
  have hc := card_listUnion_add_overlap _ (chain_localPairs (allowed := allowed) regions h)
  rw [localPairs_zipWith] at hc
  simp only [List.map_map, Function.comp_def] at hc
  exact hc

end D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection
