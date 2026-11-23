/- GID: D5/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Matroids/RankThreeSaturatedTopGap
   mirror-E: none(waiver:algebraic-inference)
   anchors: []
   utility: none
   digest: Six-cycle leaves yield the top gap in saturated ternary internal extensions. -/

import D5.S3.Combinatorics.Matroids.RankThreeInternalSizeSpectrum

/-! # The top gap for saturated internal extensions -/

namespace D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap

open Set
open RankThreeInternalSteinerDecomposition (IsPartialSteiner)

private def Covered {r : ℕ} (P : Set (Set (Fin r))) (a b : Fin r) : Prop :=
  ∃ s ∈ P, a ∈ s ∧ b ∈ s

private def Complete {r : ℕ} (P : Set (Set (Fin r))) : Prop :=
  ∀ a b, a ≠ b → Covered P a b

private def Maximal {r : ℕ} (P : Set (Set (Fin r))) : Prop :=
  ∀ Q, IsPartialSteiner Q → P ⊆ Q → Q = P

private theorem pair_completion {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {a b : Fin r} (ne : a ≠ b) (covered : Covered P a b) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ ({a, b, x} : Set (Fin r)) ∈ P := by
  obtain ⟨s, hs, ha, hb⟩ := covered
  have outside : ∃ x ∈ s, x ∉ ({a, b} : Set (Fin r)) := by
    by_contra! no
    have upper := Set.ncard_le_ncard (show s ⊆ {a, b} from no)
    rw [valid.1 s hs, Set.ncard_pair ne] at upper
    omega
  obtain ⟨x, hx, hne⟩ := outside
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at hne
  have sub : ({a, b, x} : Set (Fin r)) ⊆ s := by
    simpa only [insert_subset_iff, singleton_subset_iff] using And.intro ha (And.intro hb hx)
  have card : ({a, b, x} : Set (Fin r)).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨a, b, x, ne, (Ne.symm hne.1), (Ne.symm hne.2), rfl⟩
  have eq := Set.eq_of_subset_of_ncard_le sub (by rw [valid.1 s hs, card])
  exact ⟨x, hne.1, hne.2, eq.symm ▸ hs⟩

private theorem maximal_of_no_uncovered_triple {r : ℕ} {P : Set (Set (Fin r))}
    (test : ∀ a b c, a ≠ b → b ≠ c → c ≠ a →
      Covered P a b ∨ Covered P b c ∨ Covered P c a) :
    Maximal P := by
  intro Q hQ sub
  apply Subset.antisymm _ sub
  intro s hs
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Set.ncard_eq_three.mp (hQ.1 s hs)
  have transfer (u v : Fin r) (ne : u ≠ v) (hu : u ∈ ({a,b,c} : Set (Fin r)))
      (hv : v ∈ ({a,b,c} : Set (Fin r))) (cov : Covered P u v) :
      ({a,b,c} : Set (Fin r)) ∈ P := by
    obtain ⟨t, ht, htu, htv⟩ := cov
    have eq := hQ.2 _ hs t (sub ht) u v ne hu hv htu htv
    exact eq.symm ▸ ht
  rcases test a b c hab hbc hac.symm with h | h | h
  · exact transfer a b hab (by simp) (by simp) h
  · exact transfer b c hbc (by simp) (by simp) h
  · exact transfer c a hac.symm (by simp) (by simp) h

private theorem swap_at_nonblock {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) (complete : Complete P)
    {a b c : Fin r} (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (missing : ({a,b,c} : Set (Fin r)) ∉ P) :
    ∃ Q : Set (Set (Fin r)), IsPartialSteiner Q ∧ Maximal Q ∧ Q.ncard + 2 = P.ncard := by
  classical
  obtain ⟨x, hxa, hxb, hx⟩ := pair_completion valid hab (complete a b hab)
  obtain ⟨y, hyb, hyc, hy⟩ := pair_completion valid hbc (complete b c hbc)
  obtain ⟨z, hzc, hza, hz⟩ := pair_completion valid hca (complete c a hca)
  have hxc : x ≠ c := fun h => missing (by simpa [h] using hx)
  have hya : y ≠ a := by
    intro h
    apply missing
    convert hy using 1
    ext i
    simp only [h, mem_insert_iff, mem_singleton_iff]
    tauto
  have hzb : z ≠ b := by
    intro h
    apply missing
    convert hz using 1
    ext i
    simp only [h, mem_insert_iff, mem_singleton_iff]
    tauto
  let A : Set (Fin r) := {a,b,c}
  let B₀ : Set (Fin r) := {a,b,x}
  let B₁ : Set (Fin r) := {b,c,y}
  let B₂ : Set (Fin r) := {c,a,z}
  let removed : Set (Set (Fin r)) := {B₀,B₁,B₂}
  have h₀₁ : B₀ ≠ B₁ := by
    intro eq
    have mem : a ∈ B₁ := eq ▸ (show a ∈ B₀ by simp [B₀])
    simp [B₁, hab, hca.symm, hya.symm] at mem
  have h₁₂ : B₁ ≠ B₂ := by
    intro eq
    have mem : b ∈ B₂ := eq ▸ (show b ∈ B₁ by simp [B₁])
    simp [B₂, hbc, hab.symm, hzb.symm] at mem
  have h₀₂ : B₀ ≠ B₂ := by
    intro eq
    have mem : b ∈ B₂ := eq ▸ (show b ∈ B₀ by simp [B₀])
    simp [B₂, hbc, hab.symm, hzb.symm] at mem
  have hxy : x ≠ y := by
    intro eq
    exact h₀₁ (valid.2 B₀ hx B₁ hy b x hxb.symm (by simp [B₀]) (by simp [B₀])
      (by simp [B₁]) (by simp [B₁, eq]))
  have hyz : y ≠ z := by
    intro eq
    exact h₁₂ (valid.2 B₁ hy B₂ hz c y hyc.symm (by simp [B₁]) (by simp [B₁])
      (by simp [B₂]) (by simp [B₂, eq]))
  have hzx : z ≠ x := by
    intro eq
    exact h₀₂ ((valid.2 B₂ hz B₀ hx a z hza.symm (by simp [B₂]) (by simp [B₂])
      (by simp [B₀]) (by simp [B₀, eq])).symm)
  let Q := insert A (P \ removed)
  have hremoved : removed ⊆ P := by
    intro s hs
    rcases (show s = B₀ ∨ s = B₁ ∨ s = B₂ by simpa [removed] using hs) with rfl | rfl | rfl
    · exact hx
    · exact hy
    · exact hz
  have old_pair (u v : Fin r) (ne : u ≠ v) (hu : u ∈ A) (hv : v ∈ A) :
      ∃ s ∈ removed, u ∈ s ∧ v ∈ s := by
    simp only [A, mem_insert_iff, mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact (ne rfl).elim
    · exact ⟨B₀, by simp [removed], by simp [B₀], by simp [B₀]⟩
    · exact ⟨B₂, by simp [removed], by simp [B₂], by simp [B₂]⟩
    · exact ⟨B₀, by simp [removed], by simp [B₀], by simp [B₀]⟩
    · exact (ne rfl).elim
    · exact ⟨B₁, by simp [removed], by simp [B₁], by simp [B₁]⟩
    · exact ⟨B₂, by simp [removed], by simp [B₂], by simp [B₂]⟩
    · exact ⟨B₁, by simp [removed], by simp [B₁], by simp [B₁]⟩
    · exact (ne rfl).elim
  have no_overlap {u v : Fin r} (ne : u ≠ v) (hu : u ∈ A) (hv : v ∈ A)
      {t : Set (Fin r)} (ht : t ∈ P \ removed) (htu : u ∈ t) (htv : v ∈ t) : False := by
    obtain ⟨s, hs, hsu, hsv⟩ := old_pair u v ne hu hv
    exact ht.2 (valid.2 s (hremoved hs) t ht.1 u v ne hsu hsv htu htv ▸ hs)
  have validQ : IsPartialSteiner Q := by
    constructor
    · intro s hs
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
      · exact Set.ncard_eq_three.mpr ⟨a, b, c, hab, hca.symm, hbc, rfl⟩
      · exact valid.1 s hs.1
    · intro s hs t ht u v ne hsu hsv htu htv
      rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs <;>
        rcases (show t = A ∨ t ∈ P \ removed from ht) with rfl | ht
      · rfl
      · exact (no_overlap ne hsu hsv ht htu htv).elim
      · exact (no_overlap ne htu htv hs hsu hsv).elim
      · exact valid.2 s hs.1 t ht.1 u v ne hsu hsv htu htv
  have leave (u v : Fin r) (ne : u ≠ v) :
      ¬ Covered Q u v ↔
        (u = x ∧ (v = a ∨ v = b)) ∨ (v = x ∧ (u = a ∨ u = b)) ∨
        (u = y ∧ (v = b ∨ v = c)) ∨ (v = y ∧ (u = b ∨ u = c)) ∨
        (u = z ∧ (v = c ∨ v = a)) ∨ (v = z ∧ (u = c ∨ u = a)) := by
    have law : ¬ Covered Q u v ↔
        (¬ (u ∈ A ∧ v ∈ A)) ∧ ∃ t ∈ removed, u ∈ t ∧ v ∈ t := by
      constructor
      · intro unseen
        refine ⟨fun h => unseen ⟨A, by simp [Q], h.1, h.2⟩, ?_⟩
        obtain ⟨s, hs, hu, hv⟩ := complete u v ne
        by_cases h : s ∈ removed
        · exact ⟨s, h, hu, hv⟩
        · exact (unseen ⟨s, Or.inr ⟨hs, h⟩, hu, hv⟩).elim
      · rintro ⟨notBoth, t, ht, htu, htv⟩ ⟨s, hs, hsu, hsv⟩
        rcases (show s = A ∨ s ∈ P \ removed from hs) with rfl | hs
        · exact notBoth ⟨hsu, hsv⟩
        · exact hs.2 (valid.2 t (hremoved ht) s hs.1 u v ne htu htv hsu hsv ▸ ht)
    rw [law]
    have removed_pair :
        (∃ t ∈ removed, u ∈ t ∧ v ∈ t) ↔
          (u ∈ B₀ ∧ v ∈ B₀) ∨ (u ∈ B₁ ∧ v ∈ B₁) ∨ (u ∈ B₂ ∧ v ∈ B₂) := by
      constructor
      · rintro ⟨t, ht, hu, hv⟩
        rcases (show t = B₀ ∨ t = B₁ ∨ t = B₂ from ht) with rfl | rfl | rfl
        · exact Or.inl ⟨hu, hv⟩
        · exact Or.inr (Or.inl ⟨hu, hv⟩)
        · exact Or.inr (Or.inr ⟨hu, hv⟩)
      · rintro (⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩)
        · exact ⟨B₀, by simp [removed], hu, hv⟩
        · exact ⟨B₁, by simp [removed], hu, hv⟩
        · exact ⟨B₂, by simp [removed], hu, hv⟩
    rw [removed_pair]
    simp only [A, B₀, B₁, B₂, mem_insert_iff, mem_singleton_iff]
    clear * - ne hab hbc hca hxa hxb hxc hya hyb hyc hza hzb hzc
    constructor
    · rintro ⟨n, ⟨hu,hv⟩ | ⟨hu,hv⟩ | ⟨hu,hv⟩⟩ <;>
        rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
        simp_all
    · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
        ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩) <;>
        simp_all
  let vertex : Fin 6 → Fin r := [a, x, b, y, c, z].get
  have distinct : [a, x, b, y, c, z].Nodup := by
    simp [List.nodup_cons, hxa.symm, hab, hya.symm, hca.symm, hza.symm,
      hxb, hxy, hxc, hzx.symm, hyb.symm, hbc, hzb.symm, hyc, hyz, hzc.symm]
  have injective : Function.Injective vertex := distinct.injective_get
  have cycle (u v : Fin r) (ne : u ≠ v) :
      ¬ Covered Q u v ↔ ∃ i : Fin 6,
        (u = vertex i ∧ v = vertex (i + 1)) ∨ (v = vertex i ∧ u = vertex (i + 1)) := by
    rw [leave u v ne]
    constructor
    · rintro (⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ |
        ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl⟩)
      · exact ⟨0, Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨1, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨0, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨1, Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨2, Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨3, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨2, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨3, Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨4, Or.inr ⟨rfl,rfl⟩⟩
      · exact ⟨5, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨4, Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨5, Or.inr ⟨rfl,rfl⟩⟩
    · rintro ⟨i,h⟩
      fin_cases i
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)
        · exact Or.inl ⟨rfl, Or.inl rfl⟩
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inl ⟨rfl, Or.inr rfl⟩
        · exact Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩)))
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, Or.inl rfl⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl rfl⟩))))
      · rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr rfl⟩))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, Or.inr rfl⟩)))))
  let evenIndices : Set (Fin 6) := {0, 2, 4}
  let color := vertex '' evenIndices
  have on_side (i : Fin 6) : vertex i ∈ color ↔ i ∈ evenIndices := by
    constructor
    · rintro ⟨j,hj,eq⟩
      exact injective eq ▸ hj
    · intro hi
      exact ⟨i,hi,rfl⟩
  have alternates (i : Fin 6) : vertex i ∈ color ↔ vertex (i + 1) ∉ color := by
    rw [on_side, on_side]
    fin_cases i <;> decide
  have opposite (u v : Fin r) (ne : u ≠ v) (uncovered : ¬Covered Q u v) :
      u ∈ color ↔ v ∉ color := by
    obtain ⟨i, ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (cycle u v ne).mp uncovered
    · exact alternates i
    · have h := alternates i
      tauto
  have maxQ : Maximal Q := by
    apply maximal_of_no_uncovered_triple
    intro u v w huv hvw hwu
    by_contra! ht
    have p := opposite u v huv ht.1
    have q := opposite v w hvw ht.2.1
    have s := opposite w u hwu ht.2.2
    tauto
  have removedCard : removed.ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨B₀, B₁, B₂, h₀₁, h₀₂, h₁₂, rfl⟩
  have missingResidual : A ∉ P \ removed := fun h => missing h.1
  have count := Set.ncard_sdiff_add_ncard_of_subset hremoved
  refine ⟨Q, validQ, maxQ, ?_⟩
  rw [show Q = insert A (P \ removed) from rfl, Set.ncard_insert_of_notMem missingResidual]
  omega


private theorem ncard_disjoint_union_const {ι α : Type*} [Finite ι] [Finite α]
    (indices : Set ι) (pieces : ι → Set α) (h : indices.PairwiseDisjoint pieces)
    (k : ℕ) (card : ∀ i ∈ indices, (pieces i).ncard = k) :
    (⋃ i ∈ indices, pieces i).ncard = indices.ncard * k := by
  classical
  let hf := Set.toFinite indices
  rw [hf.ncard_biUnion (fun i _ => Set.toFinite (pieces i)) h,
    finsum_mem_congr rfl card, finsum_mem_eq_finite_toFinset_sum _ hf,
    Set.ncard_eq_toFinset_card indices hf]
  simp

private theorem offDiag_ncard {α : Type*} [Finite α] (s : Set α) :
    s.offDiag.ncard = s.ncard * s.ncard - s.ncard := by
  classical
  let f := (Set.toFinite s).toFinset
  have coe : (f : Set α) = s := (Set.toFinite s).coe_toFinset
  rw [← coe, ← Finset.coe_offDiag, Set.ncard_coe_finset, Finset.offDiag_card]
  simp

private def Uncovered {r : ℕ} (P : Set (Set (Fin r))) (a b : Fin r) : Prop :=
  a ≠ b ∧ ¬ Covered P a b

private def leaveNeighbors {r : ℕ} (P : Set (Set (Fin r))) (a : Fin r) : Set (Fin r) :=
  {b | Uncovered P a b}

private theorem uncovered_symm {r : ℕ} {P : Set (Set (Fin r))} {a b : Fin r}
    (h : Uncovered P a b) : Uncovered P b a :=
  ⟨h.1.symm, fun ⟨s,hs,hb,ha⟩ => h.2 ⟨s,hs,ha,hb⟩⟩

private theorem packing_leave_count {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) :
    ({p : Fin r × Fin r | Uncovered P p.1 p.2} : Set _).ncard + 6 * P.ncard =
      r * r - r := by
  let used : Set (Fin r × Fin r) := ⋃ b ∈ P, b.offDiag
  have usedCard : used.ncard = P.ncard * 6 := by
    apply ncard_disjoint_union_const
    · intro s hs t ht different
      refine Set.disjoint_left.mpr ?_
      intro p hps hpt
      exact different (valid.2 s hs t ht _ _ hps.2.2 hps.1 hps.2.1 hpt.1 hpt.2.1)
    · intro s hs
      rw [offDiag_ncard, valid.1 s hs]
  let allPairs := (univ : Set (Fin r)).offDiag
  have sub : used ⊆ allPairs := by
    intro p hp
    obtain ⟨s, hs, pair⟩ := Set.mem_iUnion₂.mp hp
    exact ⟨trivial, trivial, pair.2.2⟩
  have leave : allPairs \ used = {p : Fin r × Fin r | Uncovered P p.1 p.2} := by
    ext p
    simp only [allPairs, used, mem_sdiff, mem_offDiag, mem_univ, true_and, mem_iUnion,
      mem_ofPred_eq, Uncovered, Covered]
    constructor
    · rintro ⟨ne, notUsed⟩
      exact ⟨ne, fun ⟨s, hs, ha, hb⟩ => notUsed ⟨s, hs, ha, hb, ne⟩⟩
    · rintro ⟨ne, notUsed⟩
      exact ⟨ne, fun ⟨s, hs, ha, hb, _⟩ => notUsed ⟨s, hs, ha, hb⟩⟩
  have count := Set.ncard_sdiff_add_ncard_of_subset sub
  rw [leave, usedCard, offDiag_ncard] at count
  simpa [Nat.mul_comm] using count

private theorem vertex_leave_count {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) (a : Fin r) :
    (leaveNeighbors P a).ncard + 2 * ({s ∈ P | a ∈ s} : Set _).ncard + 1 = r := by
  let incidence : Set (Set (Fin r)) := {s ∈ P | a ∈ s}
  let used : Set (Fin r) := ⋃ s ∈ incidence, s \ {a}
  have usedCard : used.ncard = incidence.ncard * 2 := by
    apply ncard_disjoint_union_const
    · intro s hs t ht different
      refine Set.disjoint_left.mpr ?_
      intro b hbs hbt
      have ne : b ≠ a := fun h => hbs.2 (by simp [h])
      exact different (valid.2 s hs.1 t ht.1 b a ne hbs.1 hs.2 hbt.1 ht.2)
    · intro s hs
      have card := Set.ncard_sdiff_singleton_add_one hs.2
      rw [valid.1 s hs.1] at card
      omega
  let others := (univ : Set (Fin r)) \ {a}
  have sub : used ⊆ others := by
    intro b hb
    obtain ⟨s, _, h⟩ := Set.mem_iUnion₂.mp hb
    exact ⟨trivial, h.2⟩
  have leave : others \ used = leaveNeighbors P a := by
    ext b
    simp only [others, used, incidence, mem_sdiff, mem_univ, mem_singleton_iff,
      true_and, mem_iUnion, mem_ofPred_eq, leaveNeighbors, Uncovered, Covered]
    constructor
    · rintro ⟨ne, notUsed⟩
      exact ⟨Ne.symm ne, fun ⟨s, hs, ha, hb⟩ => notUsed ⟨s, ⟨hs, ha⟩, hb, ne⟩⟩
    · rintro ⟨ne, notUsed⟩
      exact ⟨Ne.symm ne, fun ⟨s, ⟨hs, ha⟩, hb, _⟩ => notUsed ⟨s, hs, ha, hb⟩⟩
  have count := Set.ncard_sdiff_add_ncard_of_subset sub
  rw [leave, usedCard] at count
  have othersCard := Set.ncard_sdiff_singleton_add_one (Set.mem_univ a)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at othersCard
  change others.ncard + 1 = r at othersCard
  change (leaveNeighbors P a).ncard + 2 * incidence.ncard + 1 = r
  omega

private theorem triangle_in_three_edges {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) (odd : r % 2 = 1)
    (three : ({p : Fin r × Fin r | Uncovered P p.1 p.2} : Set _).ncard = 6) :
    ∃ a b c, Uncovered P a b ∧ Uncovered P b c ∧ Uncovered P c a := by
  classical
  let deg (a : Fin r) := (leaveNeighbors P a).ncard
  let active := Finset.univ.filter (fun a : Fin r => 0 < deg a)
  have count := RankThreeInternalSizeSpectrum.fibers_card_eq (leaveNeighbors P)
  have sum_degree : ∑ a : Fin r, deg a = 6 := count.symm.trans three
  have even_degree (a : Fin r) : deg a % 2 = 0 := by
    have h := vertex_leave_count valid a
    change deg a + _ + 1 = r at h
    omega
  have degree_two (a : Fin r) (pos : 0 < deg a) : 2 ≤ deg a := by
    have := even_degree a
    omega
  have active_card : active.card ≤ 3 := by
    have filtered : ∑ a ∈ active, deg a ≤ 6 := by
      rw [← sum_degree]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have lower : active.card * 2 ≤ ∑ a ∈ active, deg a := by
      calc
        active.card * 2 = ∑ _a ∈ active, 2 := by simp
        _ ≤ _ := Finset.sum_le_sum (fun a ha => degree_two a (Finset.mem_filter.mp ha).2)
    omega
  have active_of {a b : Fin r} (h : Uncovered P a b) : a ∈ active := by
    have pos : 0 < deg a := (Set.ncard_pos (Set.toFinite (leaveNeighbors P a))).mpr ⟨b,h⟩
    simp [active, pos]
  have second {a b : Fin r} (h : Uncovered P a b) :
      ∃ c, c ≠ b ∧ Uncovered P a c := by
    by_contra! no
    have sub : leaveNeighbors P a ⊆ {b} := by
      intro c hc
      change c = b
      by_contra ne
      exact no c ne hc
    have upper := Set.ncard_le_ncard sub
    rw [Set.ncard_singleton] at upper
    have lower := degree_two a (Finset.mem_filter.mp (active_of h)).2
    change deg a ≤ 1 at upper
    omega
  obtain ⟨⟨a,b⟩, hab⟩ := Set.nonempty_of_ncard_ne_zero (by rw [three]; decide)
  change Uncovered P a b at hab
  obtain ⟨c, hcb, hac⟩ := second hab
  have sub : ({a,b,c} : Finset (Fin r)) ⊆ active := by
    intro i hi
    rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hi :
      i = a ∨ i = b ∨ i = c) with rfl | rfl | rfl
    · exact active_of hab
    · exact active_of (uncovered_symm hab)
    · exact active_of (uncovered_symm hac)
  have cardinal : ({a,b,c} : Finset (Fin r)).card = 3 := by
    simp [Finset.card_insert_of_notMem, hab.1, hac.1, hcb.symm]
  have all := Finset.eq_of_subset_of_card_le sub (by omega)
  obtain ⟨d, hda, hbd⟩ := second (uncovered_symm hab)
  have hd : d ∈ ({a,b,c} : Finset (Fin r)) := all ▸ active_of (uncovered_symm hbd)
  have eq : d = c := by
    simpa [Finset.mem_insert, Finset.mem_singleton, hda, hbd.1.symm] using hd
  exact ⟨a,b,c,hab,eq ▸ hbd,uncovered_symm hac⟩

private theorem insert_uncovered_triangle {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) {a b c : Fin r}
    (ab : Uncovered P a b) (bc : Uncovered P b c) (ca : Uncovered P c a) :
    IsPartialSteiner (insert ({a,b,c} : Set (Fin r)) P) := by
  classical
  let A : Set (Fin r) := {a,b,c}
  have noPair {s : Set (Fin r)} (hs : s ∈ P) {u v : Fin r} (ne : u ≠ v)
      (hu : u ∈ A) (hv : v ∈ A) (hsu : u ∈ s) (hsv : v ∈ s) : False := by
    simp only [A, mem_insert_iff, mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact ne rfl
    · exact ab.2 ⟨s,hs,hsu,hsv⟩
    · exact ca.2 ⟨s,hs,hsv,hsu⟩
    · exact ab.2 ⟨s,hs,hsv,hsu⟩
    · exact ne rfl
    · exact bc.2 ⟨s,hs,hsu,hsv⟩
    · exact ca.2 ⟨s,hs,hsu,hsv⟩
    · exact bc.2 ⟨s,hs,hsv,hsu⟩
    · exact ne rfl
  constructor
  · intro s hs
    rcases (show s = A ∨ s ∈ P from hs) with rfl | hs
    · exact Set.ncard_eq_three.mpr ⟨a,b,c,ab.1,ca.1.symm,bc.1,rfl⟩
    · exact valid.1 s hs
  · intro s hs t ht u v ne hsu hsv htu htv
    rcases (show s = A ∨ s ∈ P from hs) with rfl | hs <;>
      rcases (show t = A ∨ t ∈ P from ht) with rfl | ht
    · rfl
    · exact (noPair ht ne hsu hsv htu htv).elim
    · exact (noPair hs ne htu htv hsu hsv).elim
    · exact valid.2 s hs t ht u v ne hsu hsv htu htv


private theorem complete_count {r : ℕ} {P : Set (Set (Fin r))}
    (valid : IsPartialSteiner P) (complete : Complete P) :
    6 * P.ncard = r * r - r := by
  have empty : ({p : Fin r × Fin r | Uncovered P p.1 p.2} : Set _) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p h
    exact h.2 (complete _ _ h.1)
  simpa [empty] using packing_leave_count valid

private theorem complete_odd {r : ℕ} {P : Set (Set (Fin r))}
    (positive : 0 < r) (valid : IsPartialSteiner P) (complete : Complete P) : r % 2 = 1 := by
  let a : Fin r := ⟨0, positive⟩
  have empty : leaveNeighbors P a = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro b h
    exact h.2 (complete a b h.1)
  have count := vertex_leave_count valid a
  rw [empty, Set.ncard_empty, zero_add] at count
  omega

private theorem local_bound_gap {r : ℕ} {P Q : Set (Set (Fin r))}
    (valid : IsPartialSteiner Q) (maximal : Maximal Q) (odd : r % 2 = 1)
    (completeCard : 6 * P.ncard = r * r - r) :
    Q.ncard ≤ P.ncard ∧ Q.ncard + 1 ≠ P.ncard := by
  have count := packing_leave_count valid
  constructor
  · omega
  · intro short
    have leaveCard : ({p : Fin r × Fin r | Uncovered Q p.1 p.2} : Set _).ncard = 6 := by
      omega
    obtain ⟨a,b,c,ab,bc,ca⟩ := triangle_in_three_edges valid odd leaveCard
    let A : Set (Fin r) := {a,b,c}
    have same : insert A Q = Q :=
      maximal _ (insert_uncovered_triangle valid ab bc ca) (Set.subset_insert _ _)
    have hA : A ∈ Q := same ▸ Set.mem_insert _ _
    exact ab.2 ⟨A, hA, by simp [A], by simp [A]⟩

private theorem exists_nonblock {r : ℕ} {P : Set (Set (Fin r))}
    (large : 3 < r) (valid : IsPartialSteiner P) (complete : Complete P) :
    ∃ a b c : Fin r, a ≠ b ∧ b ≠ c ∧ c ≠ a ∧ ({a,b,c} : Set (Fin r)) ∉ P := by
  let a : Fin r := ⟨0, by omega⟩
  let b : Fin r := ⟨1, by omega⟩
  have hab : a ≠ b := by
    intro eq
    exact Nat.zero_ne_one (congrArg Fin.val eq)
  obtain ⟨s, hs, ha, hb⟩ := complete a b hab
  have outside : ∃ c, c ∉ s := by
    by_contra! full
    have same : s = univ := Set.eq_univ_of_forall full
    have n := valid.1 s hs
    simp [same, Set.ncard_univ, Nat.card_eq_fintype_card] at n
    omega
  obtain ⟨c, hc⟩ := outside
  refine ⟨a,b,c,hab,fun h => hc (h ▸ hb),fun h => hc (h.symm ▸ ha),?_⟩
  intro h
  have eq := valid.2 _ h s hs a b hab (by simp) (by simp) ha hb
  exact hc (eq ▸ (show c ∈ ({a,b,c} : Set (Fin r)) by simp))

open RankThreeInternalTriplePotentials (Row LiftedLineFamily)
open RankThreeOmissionPotentials (covers)
open RankThreeInternalSteinerDecomposition (extendedFamily)
open RankThreeInternalSizeSpectrum
open D5.S3.Combinatorics.LatinEulerianMultiples (IsLatin)

/-- The two largest saturated sizes differ by two when a class admits a complete Steiner system. -/
theorem saturated_top_gap {d r : ℕ} [NeZero (3 * r)] {T : Type*}
    (hd : 0 < d) (hr : 7 ≤ r)
    (mixed : T → Fin 3 → Row d × ZMod (3 * r))
    (family : LiftedLineFamily mixed)
    (crosses : ∀ t, Function.Injective (fun i => (mixed t i).1))
    (mixedUnique : ∀ t u x y, x ≠ y → covers (mixed t) x y → covers (mixed u) x y → t = u)
    (S : Set (Set (Fin r))) (hS : IsPartialSteiner S)
    (complete : ∀ a b : Fin r, a ≠ b → ∃ t ∈ S, a ∈ t ∧ b ∈ t) :
    let N := 3 ^ d * r ^ 2 + 3 ^ (d + 1) * (r * (r - 1) / 6)
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard = N) ∧
    (∃ G, IsSaturatedInternalExtension mixed G ∧ G.ncard + 2 = N) ∧
    (∀ G, IsSaturatedInternalExtension mixed G → G.ncard ≤ N ∧ G.ncard + 1 ≠ N) := by
  classical
  intro N
  let I := Row d × ZMod 3
  let M := S.ncard
  have cardS : 6 * M = r * r - r := complete_count hS complete
  have odd := complete_odd (by omega : 0 < r) hS complete
  have form : M = r * (r - 1) / 6 := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, ← cardS]
    omega
  have classes : Fintype.card I = 3 ^ (d + 1) := by
    simp [I, Row, Fintype.card_prod, pow_succ]
  have N_eq : N = 3 ^ d * r ^ 2 + Fintype.card I * M := by
    simp only [N, classes, form]
  have maxS : Maximal S := maximal_of_no_uncovered_triple (fun a b _ hab _ _ =>
    Or.inl (complete a b hab))
  obtain ⟨a,b,c,hab,hbc,hca,missing⟩ := exists_nonblock (by omega : 3 < r) hS complete
  obtain ⟨S',hS',maxS',cardS'⟩ := swap_at_nonblock hS complete hab hbc hca missing
  let : NeZero r := ⟨by omega⟩
  obtain ⟨labels,hlabels⟩ := RankThreeMinimumInternalAdditions.residue_indexing r
  let e : Row d → (ZMod (3 * r) ≃ ZMod 3 × Fin r) := fun _ => labels
  have he (x : Row d) (a : ZMod (3 * r)) :
      (e x a).1 = ZMod.castHom (dvd_mul_right 3 r) (ZMod 3) a := hlabels a
  let bridge := saturated_internal_extension_iff e he hd mixed family crosses mixedUnique
  obtain ⟨square,latin⟩ := latin_exists r
  let L : Row d → Fin r → Fin r → Fin r := fun _ => square
  have count (K : Row d → Fin r → Fin r → Fin r) (P : Row d → ZMod 3 → Set (Set (Fin r)))
      (valid : ∀ x c, IsPartialSteiner (P x c)) :
      (extendedFamily e K P).ncard = 3 ^ d * r ^ 2 + ∑ i : I, (P i.1 i.2).ncard := by
    rw [counting_decomposition e K P valid, packingEntries,
      fibers_card_eq (fun i : I => P i.1 i.2)]
  let P₀ : Row d → ZMod 3 → Set (Set (Fin r)) := fun _ _ => S
  have full : IsSaturatedInternalExtension mixed (extendedFamily e L P₀) :=
    (bridge _).mpr ⟨L,P₀,fun _ => latin,fun _ _ => hS,fun _ _ => maxS,rfl⟩
  have full_size : (extendedFamily e L P₀).ncard = N := by
    rw [count L P₀ (fun _ _ => hS), N_eq]
    simp [P₀, M]
  let idx : I := (0,0)
  let P₁ (x : Row d) (c : ZMod 3) := if (x,c) = idx then S' else S
  have valid₁ (x : Row d) (c : ZMod 3) : IsPartialSteiner (P₁ x c) := by
    by_cases h : (x,c) = idx <;> simp [P₁,h,hS,hS']
  have max₁ (x : Row d) (c : ZMod 3) : Maximal (P₁ x c) := by
    by_cases h : (x,c) = idx <;> simp [P₁,h,maxS,maxS']
  have small : IsSaturatedInternalExtension mixed (extendedFamily e L P₁) :=
    (bridge _).mpr ⟨L,P₁,fun _ => latin,valid₁,max₁,rfl⟩
  have small_size : (extendedFamily e L P₁).ncard + 2 = N := by
    rw [count L P₁ valid₁, ← full_size, count L P₀ (fun _ _ => hS)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ idx),
      ← Finset.sum_erase_add (f := fun i : I => (P₀ i.1 i.2).ncard) _ (Finset.mem_univ idx)]
    have eq : ∑ i ∈ Finset.univ.erase idx, (P₁ i.1 i.2).ncard =
        ∑ i ∈ Finset.univ.erase idx, (P₀ i.1 i.2).ncard := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp [P₁, P₀, (Finset.mem_erase.mp hi).1]
    rw [eq]
    simp only [P₁, P₀, Prod.mk.eta, ite_true]
    omega
  refine ⟨⟨_,full,full_size⟩,⟨_,small,small_size⟩,?_⟩
  intro G hG
  obtain ⟨K,P,_,valid,maximal,rfl⟩ := (bridge G).mp hG
  let size (i : I) := (P i.1 i.2).ncard
  have hlocal (i : I) : size i ≤ M ∧ size i + 1 ≠ M :=
    local_bound_gap (valid i.1 i.2) (maximal i.1 i.2) odd cardS
  have decomp :
      (extendedFamily e K P).ncard = 3 ^ d * r ^ 2 + ∑ i : I, size i := count K P valid
  have sum_capacity : ∑ i : I, M = Fintype.card I * M := by simp
  constructor
  · rw [decomp, N_eq, ← sum_capacity]
    exact Nat.add_le_add_left (Finset.sum_le_sum (fun i _ => (hlocal i).1)) _
  · intro bad
    let deficit (i : I) := M - size i
    have total : ∑ i : I, deficit i + ∑ i : I, size i = Fintype.card I * M := by
      rw [← sum_capacity, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => Nat.sub_add_cancel (hlocal i).1)
    have one : ∑ i : I, deficit i = 1 := by rw [decomp, N_eq] at bad; omega
    have zero (i : I) : deficit i = 0 := by
      have single : deficit i ≤ ∑ j : I, deficit j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (deficit j)) (Finset.mem_univ i)
      have le := (hlocal i).1
      have ne := (hlocal i).2
      unfold deficit at *
      rw [one] at single
      omega
    simp [zero] at one

end D5.S3.Combinatorics.Matroids.RankThreeSaturatedTopGap
