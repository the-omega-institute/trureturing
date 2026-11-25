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
    ∀ regions : List (Finset A),
      let count := (listUnion regions).card +
        (regions.zipWith (fun s t => (s ∩ t).card) regions.tail).sum
      let total := (regions.map Finset.card).sum
      count ≤ total ∧ (count = total ↔ RunningIntersection regions)
  | [] => by simp [listUnion, RunningIntersection]
  | [_] => by simp [listUnion, RunningIntersection]
  | x :: y :: tail => by
    have unionCount := Finset.card_union_add_card_inter x (listUnion (y :: tail))
    have sub : x ∩ y ⊆ x ∩ listUnion (y :: tail) := by
      intro i hi
      obtain ⟨hx, hy⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_inter.mpr ⟨hx, (mem_listUnion _ _).mpr ⟨y, by simp, hy⟩⟩
    have overlapLe := Finset.card_le_card sub
    obtain ⟨tailLe, tailEq⟩ := card_listUnion_add_overlap (y :: tail)
    dsimp only
    simp only [List.tail_cons, List.zipWith_cons_cons, List.map_cons, List.sum_cons]
      at tailLe tailEq ⊢
    change ((x ∪ listUnion (y :: tail)).card + _) ≤ _ ∧
      (((x ∪ listUnion (y :: tail)).card + _) = _ ↔ _)
    refine ⟨by omega, ?_⟩
    constructor
    · intro h
      refine ⟨?_, tailEq.mp (by omega)⟩
      have overlapEq := Finset.eq_of_subset_of_card_le sub (by omega)
      intro z hz i hi
      obtain ⟨hx, hz'⟩ := Finset.mem_inter.mp hi
      have hu := (mem_listUnion (y :: tail) i).mpr ⟨z, List.mem_cons_of_mem y hz, hz'⟩
      exact (Finset.mem_inter.mp
        (overlapEq ▸ Finset.mem_inter.mpr ⟨hx, hu⟩ : i ∈ x ∩ y)).2
    · rintro ⟨head, rest⟩
      rw [adjacent_intersection x y tail head] at unionCount
      have he := tailEq.mpr rest
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

private theorem mem_localPairs {allowed : Finset V → Prop} {s : Finset V}
    {p : LegalPair allowed} : p ∈ localPairs allowed s ↔ occupied p.1 ⊆ s := by
  simp [localPairs]

/-- Sites whose singleton word is legal. -/
noncomputable def admittedSites (allowed : Finset V → Prop) : Finset V := by
  classical
  exact Finset.univ.filter (fun i => allowed {i})

omit [DecidableEq V] in
private theorem mem_admittedSites {allowed : Finset V → Prop} {i : V} :
    i ∈ admittedSites allowed ↔ allowed {i} := by
  simp [admittedSites]

private theorem occupied_admitted {allowed : Finset V → Prop} (closed : DownwardClosed allowed)
    (p : LegalPair allowed) : occupied p.1 ⊆ admittedSites allowed := by
  intro i hi
  apply mem_admittedSites.mpr
  rcases Finset.mem_union.mp hi with hx | hy
  · exact closed (Finset.singleton_subset_iff.mpr hx) p.2.1
  · exact closed (Finset.singleton_subset_iff.mpr hy) p.2.2

private theorem running_localPairs_iff {allowed : Finset V → Prop} (h : DownwardClosed allowed) :
    ∀ regions : List (Finset V),
      RunningIntersection (regions.map (localPairs allowed)) ↔
        RunningIntersection (regions.map (fun s => s ∩ admittedSites allowed))
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | x :: y :: tail => by
    constructor
    · rintro ⟨head, rest⟩
      refine ⟨?_, (running_localPairs_iff h (y :: tail)).mp rest⟩
      intro region hr i hi
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hx, hz'⟩ := Finset.mem_inter.mp hi
      obtain ⟨hix, ha⟩ := Finset.mem_inter.mp hx
      have hiz := (Finset.mem_inter.mp hz').1
      have valid := mem_admittedSites.mp ha
      let p : LegalPair allowed := ⟨({i}, {i}), valid, valid⟩
      have hp : occupied p.1 = {i} := Finset.union_self _
      have hxPair : p ∈ localPairs allowed x := mem_localPairs.mpr
        (hp ▸ Finset.singleton_subset_iff.mpr hix)
      have hzPair : p ∈ localPairs allowed z := mem_localPairs.mpr
        (hp ▸ Finset.singleton_subset_iff.mpr hiz)
      have hyPair := head _ (List.mem_map.mpr ⟨z, hz, rfl⟩)
        (Finset.mem_inter.mpr ⟨hxPair, hzPair⟩)
      exact Finset.mem_inter.mpr ⟨mem_localPairs.mp hyPair (by simp [hp]), ha⟩
    · rintro ⟨head, rest⟩
      refine ⟨?_, (running_localPairs_iff h (y :: tail)).mpr rest⟩
      intro region hr p hp
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hr
      obtain ⟨hx, hz'⟩ := Finset.mem_inter.mp hp
      apply mem_localPairs.mpr
      intro i hi
      have ha := occupied_admitted h p hi
      have hiy := head _ (List.mem_map.mpr ⟨z, hz, rfl⟩) (Finset.mem_inter.mpr
        ⟨Finset.mem_inter.mpr ⟨mem_localPairs.mp hx hi, ha⟩,
          Finset.mem_inter.mpr ⟨mem_localPairs.mp hz' hi, ha⟩⟩)
      exact (Finset.mem_inter.mp hiy).1

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

/-- Adjacent overlaps account for all repeated coordinates exactly when the regions have
running intersection on the sites with legal singleton words. -/
theorem finrank_add_adjacentOverlap_iff {allowed : Finset V → Prop}
    (closed : DownwardClosed allowed) (regions : List (Finset V)) :
    Module.finrank K (marginalMap (K := K) (allowed := allowed) {s | s ∈ regions}).range +
      (regions.zipWith (fun s t => regionPairCount allowed (s ∩ t)) regions.tail).sum =
      (regions.map (regionPairCount allowed)).sum ↔
      RunningIntersection (regions.map (fun s => s ∩ admittedSites allowed)) := by
  rw [finrank_marginalMap closed, ← count_cover allowed regions]
  have hc := (card_listUnion_add_overlap (regions.map (localPairs allowed))).2
  rw [localPairs_zipWith] at hc
  simp only [List.map_map, Function.comp_def] at hc
  exact hc.trans (running_localPairs_iff closed regions)

end D5.S3.Quantum.Entanglement.Marginals.LocalMarginalRunningIntersection
