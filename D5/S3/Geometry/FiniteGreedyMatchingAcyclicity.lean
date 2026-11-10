/- GID: D5/S3/Geometry/FiniteGreedyMatchingAcyclicity
   generality: G
   mirror-B: D5/B/S3/Geometry/FiniteGreedyMatchingAcyclicity
   mirror-E: none(waiver:relative-greedy-acyclicity)
   anchors: [mathlib/module/Mathlib.AlgebraicTopology.SimplicialComplex.Basic]
   utility: none
   digest: The literal coordinate-greedy matching is acyclic by incomparable relative branches and a no-return three-region potential. -/
import D5.S3.Geometry.FiniteCoordinateGreedyMatching

/-! UNCOMPILED. The proof uses the actual full simultaneous rounds. A and B
are relative families on the same labels. In P, v is added only upwards and
never removed downwards. No general simplicial Morse theorem is imported.
-/

noncomputable section
open Set Finset

namespace D5.S3.Geometry.FiniteGreedyMatchingAcyclicity

open FiniteAcyclicFaceMatching FiniteCoordinateGreedyMatching
open FiniteCoordinateGreedyMatching.RelativeFamily

variable {V : Type*} [Fintype V] [DecidableEq V]

def Separated (A B : Finset (Finset V)) : Prop :=
  ∀ a ∈ A, ∀ b ∈ B, ¬ a ⊆ b ∧ ¬ b ⊆ a

theorem separated_disjoint {A B : Finset (Finset V)} (h : Separated A B) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro s hs ht
  exact (h s hs s ht).1 le_rfl

theorem separated_mono {A B C D : Finset (Finset V)} (h : Separated A B)
    (hC : C ⊆ A) (hD : D ⊆ B) : Separated C D :=
  fun a ha b hb => h a (hC ha) b (hD hb)

theorem lowers_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :
    lowers (A ∪ B) v = lowers A v ∪ lowers B v := by
  ext s
  simp only [mem_lowers, Finset.mem_union]
  constructor
  · rintro ⟨hsA | hsB, hn, huA | huB⟩
    · exact Or.inl ⟨hsA, hn, huA⟩
    · exact ((h s hsA _ huB).1 (subset_insert _ _)).elim
    · exact ((h _ huA s hsB).2 (subset_insert _ _)).elim
    · exact Or.inr ⟨hsB, hn, huB⟩
  · rintro (⟨hs, hn, hu⟩ | ⟨hs, hn, hu⟩)
    · exact ⟨Or.inl hs, hn, Or.inl hu⟩
    · exact ⟨Or.inr hs, hn, Or.inr hu⟩

theorem roundPairs_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :
    roundPairs (A ∪ B) v = roundPairs A v ∪ roundPairs B v := by
  simp only [roundPairs, lowers_union h, Finset.image_union]

theorem pairedFaces_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :
    pairedFaces (A ∪ B) v = pairedFaces A v ∪ pairedFaces B v := by
  simp only [pairedFaces, lowers_union h, Finset.image_union]
  ac_rfl

theorem remaining_union {A B : Finset (Finset V)} (h : Separated A B) (v : V) :
    remaining (A ∪ B) v = remaining A v ∪ remaining B v := by
  classical
  have hd := separated_disjoint h
  have hAB : ∀ s ∈ A, s ∉ pairedFaces B v := by
    intro s hs hp
    exact Finset.disjoint_left.mp hd hs (paired_subset B v hp)
  have hBA : ∀ s ∈ B, s ∉ pairedFaces A v := by
    intro s hs hp
    exact Finset.disjoint_left.mp hd (paired_subset A v hp) hs
  ext s
  rw [remaining, pairedFaces_union h]
  simp only [Finset.mem_sdiff, Finset.mem_union, not_or]
  constructor
  · rintro ⟨hsA | hsB, hpa, hpb⟩
    · exact Or.inl ⟨hsA, hpa⟩
    · exact Or.inr ⟨hsB, hpb⟩
  · rintro (⟨hsA, hpa⟩ | ⟨hsB, hpb⟩)
    · exact ⟨Or.inl hsA, hpa, hAB s hsA⟩
    · exact ⟨Or.inr hsB, hBA s hsB, hpb⟩

/-- The split recursion is EXACTLY the original greedy algorithm. -/
theorem greedy_union {A B : Finset (Finset V)} (h : Separated A B) (vs : List V) :
    greedy (A ∪ B) vs = greedy A vs ∪ greedy B vs := by
  induction vs generalizing A B with
  | nil => simp [greedy]
  | cons v vs ih =>
      rw [greedy, roundPairs_union h, remaining_union h,
        ih (separated_mono h (remaining_subset A v) (remaining_subset B v))]
      simp only [greedy]
      ac_rfl

def HasPair (P : Finset (Finset V × V)) (a b : Finset V) : Prop :=
  ∃ v, (a,v) ∈ P ∧ b = insert v a

def Edge (F : Finset (Finset V)) (P : Finset (Finset V × V))
    (a b : Finset V) : Prop :=
  a ∈ F ∧ b ∈ F ∧ (HasPair P a b ∨ (Cover b a ∧ ¬ HasPair P b a))

theorem walk_potential {α : Type*} {r : α → α → Prop} (f : α → ℤ)
    (hf : ∀ a b, r a b → f a < f b) {a b : α} (h : Walk r a b) : f a < f b := by
  induction h with
  | one h => exact hf _ _ h
  | cons h t ih => exact lt_trans (hf _ _ h) ih

theorem acyclic_potential {α : Type*} {r : α → α → Prop} (f : α → ℤ)
    (hf : ∀ a b, r a b → f a < f b) : Acyclic r :=
  fun a ha => (lt_irrefl (f a)) (walk_potential f hf ha)

theorem walk_nondecreasing {α : Type*} {r : α → α → Prop} (z : α → Nat)
    (hz : ∀ a b, r a b → z a ≤ z b) {a b : α} (h : Walk r a b) : z a ≤ z b := by
  induction h with
  | one h => exact hz _ _ h
  | cons h t ih => exact (hz _ _ h).trans ih

theorem walk_one_zone {α : Type*} {r : α → α → Prop} (z : α → Nat)
    (hz : ∀ a b, r a b → z a ≤ z b) {a b : α} (h : Walk r a b)
    (k : Nat) (ha : z a = k) (hb : z b = k) :
    Walk (fun a b => r a b ∧ z a = k ∧ z b = k) a b := by
  revert ha hb
  induction h with
  | one h => intro ha hb; exact .one ⟨h, ha, hb⟩
  | @cons a b c h t ih =>
      intro ha hb
      have h1 := hz a b h
      have h2 := walk_nondecreasing z hz t
      have hbk : z b = k := by omega
      exact .cons ⟨h, ha, hbk⟩ (ih hbk hb)

/-- A no-return partition reduces a cycle to one region. -/
theorem acyclic_zones {α : Type*} {r : α → α → Prop} (z : α → Nat)
    (hz : ∀ a b, r a b → z a ≤ z b)
    (hk : ∀ k, Acyclic (fun a b => r a b ∧ z a = k ∧ z b = k)) : Acyclic r := by
  intro a ha
  exact hk (z a) a (walk_one_zone z hz ha (z a) rfl rfl)

namespace RelativeFamily

variable (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V)

theorem separated_branches : Separated (R.A v) (R.B v) :=
  fun _ ha _ hb => R.branches_incomparable v ha hb

theorem greedy_cons (vs : List V) : greedy R.F (v :: vs) =
    roundPairs R.F v ∪ (greedy (R.A v) vs ∪ greedy (R.B v) vs) := by
  rw [greedy, R.remaining_eq v, greedy_union (R.separated_branches v)]

def zone (s : Finset V) : Nat := if s ∈ R.A v then 0 else if s ∈ R.B v then 2 else 1

theorem zone_A {s : Finset V} (hs : s ∈ R.A v) : R.zone v s = 0 := by simp [zone, hs]

theorem zone_B {s : Finset V} (hs : s ∈ R.B v) : R.zone v s = 2 := by
  have hn : s ∉ R.A v := fun ha =>
    (R.branches_incomparable v ha hs).1 le_rfl
  simp [zone, hs, hn]

theorem zone_A_iff (s : Finset V) : R.zone v s = 0 ↔ s ∈ R.A v := by
  classical
  by_cases ha : s ∈ R.A v <;> by_cases hb : s ∈ R.B v <;> simp [zone, ha, hb]

theorem zone_B_iff (s : Finset V) : R.zone v s = 2 ↔ s ∈ R.B v := by
  classical
  by_cases ha : s ∈ R.A v
  · have hb : s ∉ R.B v := fun hb => (R.branches_incomparable v ha hb).1 le_rfl
    simp [zone, ha, hb]
  · by_cases hb : s ∈ R.B v <;> simp [zone, ha, hb]

theorem paired_not_A {s : Finset V} (hs : s ∈ pairedFaces R.F v) : s ∉ R.A v := by
  intro ha
  have hr : s ∈ remaining R.F v := by rw [R.remaining_eq v]; exact Finset.mem_union_left _ ha
  exact (Finset.mem_sdiff.mp hr).2 hs

theorem paired_not_B {s : Finset V} (hs : s ∈ pairedFaces R.F v) : s ∉ R.B v := by
  intro hb
  have hr : s ∈ remaining R.F v := by rw [R.remaining_eq v]; exact Finset.mem_union_right _ hb
  exact (Finset.mem_sdiff.mp hr).2 hs

theorem zone_P {s : Finset V} (hs : s ∈ pairedFaces R.F v) : R.zone v s = 1 := by
  simp [zone, R.paired_not_A v hs, R.paired_not_B v hs]

theorem paired_of_zone_one {s : Finset V} (hs : s ∈ R.F) (hz : R.zone v s = 1) :
    s ∈ pairedFaces R.F v := by
  classical
  by_contra hp
  have hr : s ∈ remaining R.F v := Finset.mem_sdiff.mpr ⟨hs, hp⟩
  rw [R.remaining_eq v] at hr
  rcases Finset.mem_union.mp hr with ha | hb
  · have h := R.zone_A v ha; omega
  · have h := R.zone_B v hb; omega

theorem pair_same_zone (vs : List V) {e : Finset V × V}
    (he : e ∈ greedy R.F (v::vs)) : R.zone v e.1 = R.zone v (upper e) := by
  rw [R.greedy_cons v vs] at he
  rcases Finset.mem_union.mp he with he | he
  · rw [R.zone_P v (round_incident he (Or.inl rfl)),
      R.zone_P v (round_incident he (Or.inr rfl))]
  · rcases Finset.mem_union.mp he with he | he
    · obtain ⟨hl, hu, _⟩ := greedy_endpoints _ _ he
      rw [R.zone_A v hl, R.zone_A v hu]
    · obtain ⟨hl, hu, _⟩ := greedy_endpoints _ _ he
      rw [R.zone_B v hl, R.zone_B v hu]

theorem zone_nondecreasing (vs : List V) {a b : Finset V}
    (hab : Edge R.F (greedy R.F (v::vs)) a b) : R.zone v a ≤ R.zone v b := by
  obtain ⟨ha, hb, hp | ⟨⟨w, hw, heq⟩, hn⟩⟩ := hab
  · obtain ⟨w, he, rfl⟩ := hp
    exact (R.pair_same_zone v vs he).le
  · have hba : b ⊆ a := by rw [heq]; exact subset_insert _ _
    have ha0 : b ∈ R.A v → a ∈ R.A v := fun h => R.A_upper v h ha hba
    have hb2 : a ∈ R.B v → b ∈ R.B v := fun h => R.B_lower v h hb hba
    by_cases haa : a ∈ R.A v <;> by_cases hba' : b ∈ R.A v <;>
      by_cases hab' : a ∈ R.B v <;> by_cases hbb : b ∈ R.B v <;>
      simp_all [zone]

theorem pair_in_A (vs : List V) {a b : Finset V} (ha : a ∈ R.A v)
    (hp : HasPair (greedy R.F (v::vs)) a b) : HasPair (greedy (R.A v) vs) a b := by
  obtain ⟨w, he, hu⟩ := hp
  rw [R.greedy_cons v vs] at he
  rcases Finset.mem_union.mp he with he | he
  · exact (R.paired_not_A v (round_incident he (Or.inl rfl)) ha).elim
  · rcases Finset.mem_union.mp he with he | he
    · exact ⟨w, he, hu⟩
    · exact ((R.branches_incomparable v ha (greedy_endpoints _ _ he).1).1 le_rfl).elim

theorem pair_in_B (vs : List V) {a b : Finset V} (ha : a ∈ R.B v)
    (hp : HasPair (greedy R.F (v::vs)) a b) : HasPair (greedy (R.B v) vs) a b := by
  obtain ⟨w, he, hu⟩ := hp
  rw [R.greedy_cons v vs] at he
  rcases Finset.mem_union.mp he with he | he
  · exact (R.paired_not_B v (round_incident he (Or.inl rfl)) ha).elim
  · rcases Finset.mem_union.mp he with he | he
    · exact ((R.branches_incomparable v (greedy_endpoints _ _ he).1 ha).1 le_rfl).elim
    · exact ⟨w, he, hu⟩

theorem edge_in_A (vs : List V) {a b : Finset V}
    (ha : a ∈ R.A v) (hb : b ∈ R.A v)
    (he : Edge R.F (greedy R.F (v::vs)) a b) :
    Edge (R.A v) (greedy (R.A v) vs) a b := by
  refine ⟨ha, hb, ?_⟩
  rcases he.2.2 with hp | ⟨hc, hn⟩
  · exact Or.inl (R.pair_in_A v vs ha hp)
  · refine Or.inr ⟨hc, ?_⟩
    rintro ⟨w, hw, heq⟩
    apply hn
    refine ⟨w, ?_, heq⟩
    rw [R.greedy_cons v vs]
    exact Finset.mem_union_right _ (Finset.mem_union_left _ hw)

theorem edge_in_B (vs : List V) {a b : Finset V}
    (ha : a ∈ R.B v) (hb : b ∈ R.B v)
    (he : Edge R.F (greedy R.F (v::vs)) a b) :
    Edge (R.B v) (greedy (R.B v) vs) a b := by
  refine ⟨ha, hb, ?_⟩
  rcases he.2.2 with hp | ⟨hc, hn⟩
  · exact Or.inl (R.pair_in_B v vs ha hp)
  · refine Or.inr ⟨hc, ?_⟩
    rintro ⟨w, hw, heq⟩
    apply hn
    refine ⟨w, ?_, heq⟩
    rw [R.greedy_cons v vs]
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hw)

def pRank (_R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V)) (v : V) (s : Finset V) : ℤ := (if v ∈ s then 2 else 0) - (s.card : ℤ)

theorem paired_region_increases (vs : List V) {a b : Finset V}
    (haP : a ∈ pairedFaces R.F v) (hbP : b ∈ pairedFaces R.F v)
    (he : Edge R.F (greedy R.F (v::vs)) a b) : R.pRank v a < R.pRank v b := by
  rcases he.2.2 with hp | ⟨⟨w, hwb, haw⟩, hn⟩
  · obtain ⟨w, hp, rfl⟩ := hp
    rw [R.greedy_cons v vs] at hp
    have hr : (a,w) ∈ roundPairs R.F v := by
      rcases Finset.mem_union.mp hp with hp | hp
      · exact hp
      · rcases Finset.mem_union.mp hp with hp | hp
        · exact (R.paired_not_A v haP (greedy_endpoints _ _ hp).1).elim
        · exact (R.paired_not_B v haP (greedy_endpoints _ _ hp).1).elim
    obtain ⟨hwv, hl⟩ := (mem_roundPairs R.F v (a,w)).mp hr
    have hva := ((mem_lowers R.F v a).mp hl).2.1
    subst w
    have hc := Finset.card_insert_of_notMem hva
    simp only [pRank, if_neg hva, Finset.mem_insert_self, if_true]
    omega
  · have hba : b ⊆ a := by rw [haw]; exact subset_insert _ _
    have hsame : v ∈ a ↔ v ∈ b := by
      constructor
      · intro hva
        by_contra hvb
        have hvw : v = w := (Finset.mem_insert.mp (haw ▸ hva)).resolve_right hvb
        subst w
        apply hn
        refine ⟨v, ?_, haw⟩
        rw [R.greedy_cons v vs]
        apply Finset.mem_union_left
        exact (mem_roundPairs R.F v (b,v)).mpr
          ⟨rfl, (mem_lowers R.F v b).mpr ⟨he.2.1, hvb, haw ▸ he.1⟩⟩
      · exact fun hv => hba hv
    have hc : a.card = b.card + 1 := by rw [haw]; exact Finset.card_insert_of_notMem hwb
    by_cases hva : v ∈ a
    · have hvb := hsame.mp hva
      simp only [pRank, if_pos hva, if_pos hvb]
      omega
    · have hvb : v ∉ b := fun hv => hva (hsame.mpr hv)
      simp only [pRank, if_neg hva, if_neg hvb]
      omega

end RelativeFamily

open RelativeFamily

/-- Full acyclicity of the ACTUAL coordinate greedy algorithm on any relative
complex, proved by induction on the coordinate list and the A/P/B partition. -/
theorem greedy_acyclic (R : FiniteCoordinateGreedyMatching.RelativeFamily (V := V))
    (vs : List V) : Acyclic (Edge R.F (greedy R.F vs)) := by
  induction vs generalizing R with
  | nil =>
      apply acyclic_potential (fun a => -(a.card : ℤ))
      intro a b he
      rcases he.2.2 with ⟨v, hv, _⟩ | ⟨⟨v, hv, rfl⟩, _⟩
      · simp [greedy] at hv
      · have hc := Finset.card_insert_of_notMem hv
        omega
  | cons v vs ih =>
      apply acyclic_zones (R.zone v) (fun _ _ h => R.zone_nondecreasing v vs h)
      intro k a hcycle
      have he : Edge R.F (greedy R.F (v::vs)) a a ∨ a ∈ R.F := by
        cases hcycle with
        | one h => exact Or.inl h.1
        | cons h _ => exact Or.inr h.1.1
      have haF : a ∈ R.F := he.elim (fun h => h.1) id
      have hak : R.zone v a = k := by
        cases hcycle with
        | one h => exact h.2.1
        | cons h _ => exact h.2.1
      by_cases hk0 : k = 0
      · have hA := ih (R.noBranch v)
        rw [R.noBranch_faces v] at hA
        apply hA a
        exact Walk.map id (fun x y h => R.edge_in_A v vs
          ((R.zone_A_iff v x).mp (h.2.1.trans hk0))
          ((R.zone_A_iff v y).mp (h.2.2.trans hk0)) h.1) hcycle
      · by_cases hk2 : k = 2
        · have hB := ih (R.yesBranch v)
          rw [R.yesBranch_faces v] at hB
          apply hB a
          exact Walk.map id (fun x y h => R.edge_in_B v vs
            ((R.zone_B_iff v x).mp (h.2.1.trans hk2))
            ((R.zone_B_iff v y).mp (h.2.2.trans hk2)) h.1) hcycle
        · have hk1 : k = 1 := by
            unfold RelativeFamily.zone at hak
            split_ifs at hak <;> omega
          apply acyclic_potential (R.pRank v) (fun x y h =>
            R.paired_region_increases v vs
              (R.paired_of_zone_one v h.1.1 (h.2.1.trans hk1))
              (R.paired_of_zone_one v h.1.2.1 (h.2.2.trans hk1)) h.1) a hcycle

theorem pairing_edge (K : PreAbstractSimplicialComplex V) (vs : List V) (a b : Finset V) :
    (pairing K vs).Edge a b ↔ Edge (FiniteVertexDominationCollapse.faceSet K)
      (greedy (FiniteVertexDominationCollapse.faceSet K) vs) a b := by
  have hp : ∀ a b, (∃ e ∈ (pairing K vs).pairs, a = e.1 ∧ b = upper e) ↔
      HasPair (greedy (FiniteVertexDominationCollapse.faceSet K) vs) a b := by
    intro a b
    constructor
    · rintro ⟨⟨c,v⟩, he, rfl, rfl⟩; exact ⟨v, he, rfl⟩
    · rintro ⟨v, he, rfl⟩; exact ⟨(a,v), he, rfl, rfl⟩
  simp only [Pairing.Edge, Edge, hp, FiniteVertexDominationCollapse.mem_faceSet]

/-- The generic native pairing has genuine acyclicity with no input certificate. -/
theorem pairing_acyclic (K : PreAbstractSimplicialComplex V) (vs : List V) :
    (pairing K vs).IsAcyclic := by
  have h := greedy_acyclic (nativeRelative K) vs
  rw [nativeRelative_faces K] at h
  intro a ha
  apply h a
  exact Walk.map id (fun x y he => (pairing_edge K vs x y).mp he) ha

end D5.S3.Geometry.FiniteGreedyMatchingAcyclicity
