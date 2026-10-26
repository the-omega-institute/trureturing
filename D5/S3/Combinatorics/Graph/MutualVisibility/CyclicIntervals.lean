/- GID: D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals
   mirror-E: none(waiver:no-computational-evidence)
   anchors: []
   utility: none
   digest: Proper nonempty cyclic intervals have a unique initial vertex and form disjoint deletion chains. -/

import D5.S3.Combinatorics.Graph.MutualVisibility.PairPayments

/-! Original-host mutual visibility and its finite reconfiguration geometry. -/

set_option autoImplicit false

namespace D5.S3.Combinatorics.Graph.MutualVisibility

open scoped symmDiff

private def cyclicRank {m : ℕ} (i x : Fin m) : ℕ :=
  if i.val ≤ x.val then x.val - i.val else x.val + m - i.val

private theorem cyclicRank_lt {m : ℕ} (i x : Fin m) : cyclicRank i x < m := by
  unfold cyclicRank
  split <;> omega

private theorem cyclicRank_injective {m : ℕ} (i : Fin m) :
    Function.Injective (cyclicRank i) := by
  intro x y h
  unfold cyclicRank at h
  by_cases hx : i.val ≤ x.val <;> by_cases hy : i.val ≤ y.val <;>
    simp only [hx, hy, ite_true, ite_false] at h <;>
    apply Fin.ext <;> omega

private theorem cyclicRank_surjective {m : ℕ} (i : Fin m) {j : ℕ} (hj : j < m) :
    ∃ x : Fin m, cyclicRank i x = j := by
  by_cases h : i.val + j < m
  · refine ⟨⟨i.val + j, h⟩, ?_⟩
    simp [cyclicRank]
  · refine ⟨⟨i.val + j - m, by omega⟩, ?_⟩
    simp only [cyclicRank]
    split <;> omega

private def cyclicArc {m : ℕ} (i : Fin m) (k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun x => cyclicRank i x < k

private theorem mem_cyclicArc {m : ℕ} (i x : Fin m) (k : ℕ) :
    x ∈ cyclicArc i k ↔ cyclicRank i x < k := by simp [cyclicArc]

private theorem cyclicArc_card {m : ℕ} (i : Fin m) {k : ℕ} (hk : k ≤ m) :
    (cyclicArc i k).card = k := by
  have himage : (cyclicArc i k).image (cyclicRank i) = Finset.range k := by
    ext j
    constructor
    · rintro hj
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
      exact Finset.mem_range.mpr ((mem_cyclicArc i x k).mp hx)
    · intro hj
      have hjk := Finset.mem_range.mp hj
      obtain ⟨x, hx⟩ := cyclicRank_surjective i (hjk.trans_le hk)
      exact Finset.mem_image.mpr ⟨x, (mem_cyclicArc i x k).mpr (hx ▸ hjk), hx⟩
  have hcard := congrArg Finset.card himage
  simpa [Finset.card_image_of_injective _ (cyclicRank_injective i)] using hcard

private theorem cyclicArc_full {m : ℕ} (i : Fin m) :
    cyclicArc i m = Finset.univ := by
  ext x
  simp [cyclicArc, cyclicRank_lt]

private theorem cyclicArc_initial {m : ℕ} (i : Fin m) {k : ℕ} (hk : 0 < k) :
    i ∈ cyclicArc i k := by simp [cyclicArc, cyclicRank, hk]

private def cyclicPred {m : ℕ} (x : Fin m) : Fin m :=
  if h : x.val = 0 then ⟨m - 1, by omega⟩ else ⟨x.val - 1, by omega⟩

private theorem cyclicArc_boundary {m : ℕ} (i x : Fin m) {k : ℕ}
    (hk : 0 < k) (hkm : k < m)
    (hx : x ∈ cyclicArc i k) (hp : cyclicPred x ∉ cyclicArc i k) : x = i := by
  have hx' := (mem_cyclicArc i x k).mp hx
  have hp' : k ≤ cyclicRank i (cyclicPred x) :=
    Nat.le_of_not_gt (fun h => hp ((mem_cyclicArc i _ k).mpr h))
  unfold cyclicRank at hx' hp'
  unfold cyclicPred at hp'
  by_cases hzero : x.val = 0 <;>
    simp only [hzero, dite_true, dite_false] at hp'
  all_goals
    split at hx' <;> split at hp' <;> apply Fin.ext <;> simp_all <;> omega

private theorem cyclicArc_pred_initial {m : ℕ} (i : Fin m) {k : ℕ} (hkm : k < m) :
    cyclicPred i ∉ cyclicArc i k := by
  intro hi
  have h := (mem_cyclicArc i _ k).mp hi
  unfold cyclicRank cyclicPred at h
  by_cases hz : i.val = 0 <;> simp only [hz, dite_true, dite_false] at h
  all_goals split at h <;> omega

private theorem cyclicArc_unique_start {m : ℕ} {i j : Fin m} {k l : ℕ}
    (hk : 0 < k) (hkm : k < m) (hl : 0 < l) (hlm : l < m)
    (he : cyclicArc i k = cyclicArc j l) : i = j := by
  apply cyclicArc_boundary j i hl hlm
  · rw [← he]; exact cyclicArc_initial i hk
  · rw [← he]; exact cyclicArc_pred_initial i hkm

private theorem cyclicPred_injective {m : ℕ} : Function.Injective (@cyclicPred m) := by
  intro x y he
  have hv := congrArg Fin.val he
  unfold cyclicPred at hv
  by_cases hx : x.val = 0 <;> by_cases hy : y.val = 0 <;>
    simp only [hx, hy, dite_true, dite_false] at hv <;> apply Fin.ext <;> omega

private theorem cyclicArc_coatom {m : ℕ} (i : Fin m) :
    cyclicArc i (m - 1) = Finset.univ.erase (cyclicPred i) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hsub : cyclicArc i (m - 1) ⊆ Finset.univ.erase (cyclicPred i) := by
    intro x hx
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_univ _⟩
    intro he
    subst x
    exact cyclicArc_pred_initial i (by omega) hx
  apply Finset.eq_of_subset_of_card_le hsub
  simp only [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin, cyclicArc_card i (by omega : m - 1 ≤ m)]
  exact le_rfl

private theorem cyclicArc_mono {m : ℕ} (i : Fin m) {k l : ℕ} (h : k ≤ l) :
    cyclicArc i k ⊆ cyclicArc i l := by
  intro x hx
  exact (mem_cyclicArc i x l).mpr (lt_of_lt_of_le ((mem_cyclicArc i x k).mp hx) h)

private theorem cyclicArc_extend {m : ℕ} (i : Fin m) {k : ℕ} (hk : k < m) :
    ∃ x, x ∉ cyclicArc i k ∧ cyclicArc i (k + 1) = insert x (cyclicArc i k) := by
  obtain ⟨x, hx⟩ := cyclicRank_surjective i hk
  refine ⟨x, ?_, ?_⟩
  · simp [mem_cyclicArc, hx]
  · ext y
    simp only [mem_cyclicArc, Finset.mem_insert]
    have he : y = x ↔ cyclicRank i y = k := by
      rw [← hx]
      exact ⟨congrArg (cyclicRank i), fun h => cyclicRank_injective i h⟩
    omega

def mappedArc {V : Type*} {m : ℕ} (e : Fin m ↪ V) (i : Fin m) (k : ℕ) :
    Finset V := (cyclicArc i k).map e

theorem mappedArc_card {V : Type*} {m : ℕ} (e : Fin m ↪ V) (i : Fin m)
    {k : ℕ} (hk : k ≤ m) : (mappedArc e i k).card = k := by
  simp only [mappedArc, Finset.card_map, cyclicArc_card i hk]

private theorem mappedArc_unique_start {V : Type*} {m : ℕ} (e : Fin m ↪ V)
    {i j : Fin m} {k l : ℕ} (hk : 0 < k) (hkm : k < m) (hl : 0 < l) (hlm : l < m)
    (he : mappedArc e i k = mappedArc e j l) : i = j :=
  cyclicArc_unique_start hk hkm hl hlm (Finset.map_injective e he)

private theorem mappedArc_step {V : Type*} [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (i : Fin m) {k : ℕ} (hk : k < m) :
    MixedMove H (mappedArc e i k) (mappedArc e i (k + 1)) := by
  obtain ⟨x, hx, he⟩ := cyclicArc_extend i hk
  have hn : e x ∉ mappedArc e i k := by simpa [mappedArc] using hx
  have hm := mixedMove_insert H (mappedArc e i k) hn
  simpa only [mappedArc, he, Finset.map_insert] using hm

private theorem cyclic_internal_cut_bound {V : Type*} [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (hm : 2 ≤ m)
    (hS : Visible H (Finset.univ.map e)) (C : Finset (Configuration H)) (s : Configuration H)
    (hs : CutReach (reconfiguration H) C s ⟨Finset.univ.map e, hS⟩)
    (hlow : ∀ T, CutReach (reconfiguration H) C s T → 2 ≤ T.val.card) :
    m ≤ (C.filter fun T => T.val ⊆ Finset.univ.map e).card := by
  classical
  let f (i : Fin m) (k : ℕ) : Configuration H :=
    ⟨mappedArc e i (min k m),
      visible_mono (Finset.map_subset_map.mpr (Finset.subset_univ _)) hS⟩
  have hfull (i : Fin m) : f i m = ⟨Finset.univ.map e, hS⟩ := by
    apply Subtype.ext
    simp [f, mappedArc, cyclicArc_full]
  have hend (i : Fin m) : ¬ CutReach (reconfiguration H) C s (f i 1) := by
    intro hr
    have hb := hlow _ hr
    have hc : (f i 1).val.card = 1 := by
      dsimp only [f]
      rw [min_eq_left (by omega : 1 ≤ m)]
      exact mappedArc_card e i (by omega)
    omega
  have hstep (i : Fin m) (k : ℕ) (_ : 1 ≤ k) (hk : k < m) :
      (reconfiguration H).Adj (f i k) (f i (k + 1)) := by
    change MixedMove H (mappedArc e i (min k m)) (mappedArc e i (min (k + 1) m))
    rw [min_eq_left hk.le, min_eq_left (by omega : k + 1 ≤ m)]
    exact mappedArc_step H e i hk
  have hpay (i : Fin m) : ∃ k, 1 ≤ k ∧ k < m ∧ f i k ∈ C := by
    obtain ⟨k, hk1, hkm, hcut⟩ := cutReach_chain_payment (f i) (by omega : 1 ≤ m)
      (hstep i) (Or.inl (by rw [hfull]; exact hs)) (hend i)
    have hne : k ≠ m := by
      intro he
      subst k
      rw [hfull] at hcut
      exact hs.choose_spec.choose hcut
    exact ⟨k, hk1, by omega, hcut⟩
  choose k hk1 hkm hkC using hpay
  let g (i : Fin m) : Configuration H := f i (k i)
  have hinj : Function.Injective g := by
    intro i j he
    have hval := congrArg Subtype.val he
    change mappedArc e i (min (k i) m) = mappedArc e j (min (k j) m) at hval
    rw [min_eq_left (hkm i).le, min_eq_left (hkm j).le] at hval
    exact mappedArc_unique_start e (hk1 i) (hkm i) (hk1 j) (hkm j) hval
  have hsub : Finset.univ.image g ⊆ C.filter fun T => T.val ⊆ Finset.univ.map e := by
    intro T hT
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨hkC i, ?_⟩
    exact Finset.map_subset_map.mpr (Finset.subset_univ _)
  have hc := Finset.card_le_card hsub
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin] using hc

theorem mappedArc_insert_step {V : Type*} [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (i : Fin m) {k : ℕ} (hk : k < m)
    {y : V} (hy : y ∉ Finset.univ.map e) :
    MixedMove H (insert y (mappedArc e i k)) (insert y (mappedArc e i (k + 1))) := by
  obtain ⟨x, hx, he⟩ := cyclicArc_extend i hk
  have hxy : e x ≠ y := by
    intro h
    exact hy (Finset.mem_map.mpr ⟨x, Finset.mem_univ _, h⟩)
  have hn : e x ∉ insert y (mappedArc e i k) := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hxy, by simpa [mappedArc] using hx⟩
  have hm := mixedMove_insert H (insert y (mappedArc e i k)) hn
  have ht : insert y (mappedArc e i (k + 1)) = insert (e x) (insert y (mappedArc e i k)) := by
    simp only [mappedArc, he, Finset.map_insert, Finset.insert_comm]
  rw [ht]
  exact hm

theorem cyclic_outside_cut_bound {V : Type*} [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (hm : 2 ≤ m) {y : V}
    (hy : y ∉ Finset.univ.map e) (C : Finset (Configuration H)) (s : Configuration H)
    (E : Finset (Fin m))
    (hvis : ∀ i ∈ E, Visible H (insert y (mappedArc e i (m - 1))))
    (hstart : ∀ i (hi : i ∈ E),
      CutReach (reconfiguration H) C s ⟨insert y (mappedArc e i (m - 1)), hvis i hi⟩ ∨
      (⟨insert y (mappedArc e i (m - 1)), hvis i hi⟩ : Configuration H) ∈ C)
    (hendpair : ∀ T : Configuration H, T.val.card = 2 → y ∈ T.val →
      ¬ CutReach (reconfiguration H) C s T) :
    E.card ≤ (C.filter fun T => y ∈ T.val ∧ T.val ⊆ insert y (Finset.univ.map e) ∧
      T.val ≠ insert y (Finset.univ.map e)).card := by
  classical
  let f (i : E) (k : ℕ) : Configuration H :=
    ⟨insert y (mappedArc e i.val (min k (m - 1))),
      visible_mono (Finset.insert_subset_insert y
        (Finset.map_subset_map.mpr (cyclicArc_mono i.val (min_le_right _ _)))) (hvis i.val i.property)⟩
  have hfull (i : E) : f i (m - 1) =
      ⟨insert y (mappedArc e i.val (m - 1)), hvis i.val i.property⟩ := by
    apply Subtype.ext
    simp [f]
  have hsub (i : E) (k : ℕ) : mappedArc e i.val (min k (m - 1)) ⊆ Finset.univ.map e :=
    Finset.map_subset_map.mpr (Finset.subset_univ _)
  have hnotmem (i : E) (k : ℕ) : y ∉ mappedArc e i.val (min k (m - 1)) :=
    fun h => hy (hsub i k h)
  have hend (i : E) : ¬ CutReach (reconfiguration H) C s (f i 1) := by
    apply hendpair
    · dsimp only [f]
      rw [Finset.card_insert_of_notMem (hnotmem i 1), mappedArc_card e i.val (by omega)]
      rw [min_eq_left (by omega : 1 ≤ m - 1)]
    · simp [f]
  have hstep (i : E) (k : ℕ) (_ : 1 ≤ k) (hk : k < m - 1) :
      (reconfiguration H).Adj (f i k) (f i (k + 1)) := by
    change MixedMove H (insert y (mappedArc e i.val (min k (m - 1))))
      (insert y (mappedArc e i.val (min (k + 1) (m - 1))))
    rw [min_eq_left hk.le, min_eq_left (by omega : k + 1 ≤ m - 1)]
    exact mappedArc_insert_step H e i.val (by omega) hy
  have hpay (i : E) : ∃ k, 1 ≤ k ∧ k ≤ m - 1 ∧ f i k ∈ C :=
    cutReach_chain_payment (f i) (by omega) (hstep i)
      (by rw [hfull]; exact hstart i.val i.property) (hend i)
  choose k hk1 hkm hkC using hpay
  let g (i : E) : Configuration H := f i (k i)
  have hinj : Function.Injective g := by
    intro i j he
    have hval := congrArg Subtype.val he
    change insert y (mappedArc e i.val (min (k i) (m - 1))) =
      insert y (mappedArc e j.val (min (k j) (m - 1))) at hval
    have he' := congrArg (fun T : Finset V => T.erase y) hval
    rw [Finset.erase_insert (hnotmem i (k i)), Finset.erase_insert (hnotmem j (k j))] at he'
    rw [min_eq_left (hkm i), min_eq_left (hkm j)] at he'
    apply Subtype.ext
    exact mappedArc_unique_start e (hk1 i) (by have := hkm i; omega)
      (hk1 j) (by have := hkm j; omega) he'
  have hcuts : Finset.univ.image g ⊆ C.filter fun T => y ∈ T.val ∧
      T.val ⊆ insert y (Finset.univ.map e) ∧ T.val ≠ insert y (Finset.univ.map e) := by
    intro T hT
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hT
    apply Finset.mem_filter.mpr
    refine ⟨hkC i, by simp [g, f], Finset.insert_subset_insert y (hsub i (k i)), ?_⟩
    intro he
    have hc := congrArg Finset.card he
    have hmcard : (g i).val.card ≤ m := by
      dsimp only [g, f]
      rw [Finset.card_insert_of_notMem (hnotmem i (k i)), mappedArc_card e i.val (by omega)]
      omega
    rw [Finset.card_insert_of_notMem hy, Finset.card_map, Finset.card_univ, Fintype.card_fin] at hc
    omega
  have hc := Finset.card_le_card hcuts
  simpa only [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe] using hc

private theorem mixedMove_subset_shape {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {S T : Finset V} (h : MixedMove H S T) (hsub : T ⊆ S) :
    ∃ x ∈ S, T = S.erase x := by
  rcases h.2 with htar | ⟨x, y, _, hy, _⟩
  · have hd : S ∆ T = S \ T := by
      ext z
      simp only [Finset.mem_symmDiff, Finset.mem_sdiff]
      have hz := @hsub z
      tauto
    rw [hd] at htar
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp htar
    have hxST : x ∈ S \ T := by rw [hx]; simp
    refine ⟨x, (Finset.mem_sdiff.mp hxST).1, ?_⟩
    ext z
    have hz : z ∈ S \ T ↔ z = x := by rw [hx]; simp
    simp only [Finset.mem_sdiff] at hz
    simp only [Finset.mem_erase]
    have hzs := @hsub z
    tauto
  · have he : T \ S = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr hsub
    rw [he] at hy
    simp at hy

private theorem mixedMove_outside_shape {V : Type*} [DecidableEq V] {H : SimpleGraph V}
    {S T : Finset V} (h : MixedMove H S T) {y : V} (hy : y ∈ T) (hyS : y ∉ S) :
    T ⊆ insert y S := by
  rcases h.2 with htar | ⟨x, z, _, hz, _⟩
  · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp htar
    have hya : y = a := by
      have hymem : y ∈ S ∆ T := Finset.mem_symmDiff.mpr (Or.inr ⟨hy, hyS⟩)
      simpa [ha] using hymem
    intro z hz
    by_cases hzS : z ∈ S
    · exact Finset.mem_insert_of_mem hzS
    · have hza : z = a := by
        have hzmem : z ∈ S ∆ T := Finset.mem_symmDiff.mpr (Or.inr ⟨hz, hzS⟩)
        simpa [ha] using hzmem
      exact Finset.mem_insert.mpr (Or.inl (hza.trans hya.symm))
  · have hyz : y = z := by
      have hymem : y ∈ T \ S := Finset.mem_sdiff.mpr ⟨hy, hyS⟩
      simpa [hz] using hymem
    intro a ha
    by_cases haS : a ∈ S
    · exact Finset.mem_insert_of_mem haS
    · have haz : a = z := by
        have hamem : a ∈ T \ S := Finset.mem_sdiff.mpr ⟨ha, haS⟩
        simpa [hz] using hamem
      exact Finset.mem_insert.mpr (Or.inl (haz.trans hyz.symm))

theorem degree_by_label_classes {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (S : Configuration H) :
    (reconfiguration H).degree S ≤ S.val.card +
      ∑ y ∈ Finset.univ \ S.val, (localCutClass ((reconfiguration H).neighborFinset S) S.val y).card := by
  classical
  let N := (reconfiguration H).neighborFinset S
  let I := N.filter fun T => T.val ⊆ S.val
  let Y := Finset.univ \ S.val
  let L := Y.biUnion (localCutClass N S.val)
  have hcover : N ⊆ I ∪ L := by
    intro T hT
    by_cases hsub : T.val ⊆ S.val
    · exact Finset.mem_union_left L (Finset.mem_filter.mpr ⟨hT, hsub⟩)
    · obtain ⟨y, hyT, hyS⟩ := Finset.not_subset.mp hsub
      have hmove : MixedMove H S.val T.val := (SimpleGraph.mem_neighborFinset _ _ _).mp hT
      apply Finset.mem_union_right I
      apply Finset.mem_biUnion.mpr
      exact ⟨y, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hyS⟩,
        Finset.mem_filter.mpr ⟨hT, hyT, mixedMove_outside_shape hmove hyT hyS⟩⟩
  have hI : I.card ≤ S.val.card := by
    let raw := I.image (fun T => T.val)
    have hraw : raw ⊆ S.val.image (fun x => S.val.erase x) := by
      intro T hT
      obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.mp hT
      have hQI := (Finset.mem_filter.mp hQ)
      have hmove : MixedMove H S.val Q.val := (SimpleGraph.mem_neighborFinset _ _ _).mp hQI.1
      obtain ⟨x, hx, he⟩ := mixedMove_subset_shape hmove hQI.2
      exact Finset.mem_image.mpr ⟨x, hx, he.symm⟩
    have hrawcard : raw.card = I.card := Finset.card_image_of_injective _ Subtype.val_injective
    calc
      I.card = raw.card := hrawcard.symm
      _ ≤ (S.val.image fun x => S.val.erase x).card := Finset.card_le_card hraw
      _ ≤ S.val.card := Finset.card_image_le
  have hL := Finset.card_biUnion_le (s := Y) (t := localCutClass N S.val)
  have hc := (Finset.card_le_card hcover).trans (Finset.card_union_le I L)
  have hn : N.card = (reconfiguration H).degree S := SimpleGraph.card_neighborFinset_eq_degree _ _
  rw [hn] at hc
  exact hc.trans (Nat.add_le_add hI hL)

private theorem cyclic_local_cut_bound {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (hm : 3 ≤ m)
    (hS : Visible H (Finset.univ.map e)) (C : Finset (Configuration H)) (s : Configuration H)
    (hs : CutReach (reconfiguration H) C s ⟨Finset.univ.map e, hS⟩)
    (hlow : ∀ T, CutReach (reconfiguration H) C s T → 3 ≤ T.val.card)
    (hmax : ∀ T, CutReach (reconfiguration H) C s T → T.val.card ≤ m)
    {y : V} (hy : y ∉ Finset.univ.map e) :
    (localCutClass ((reconfiguration H).neighborFinset ⟨Finset.univ.map e, hS⟩)
      (Finset.univ.map e) y).card ≤ (localCutClass C (Finset.univ.map e) y).card := by
  classical
  let S : Configuration H := ⟨Finset.univ.map e, hS⟩
  let N := (reconfiguration H).neighborFinset S
  let L := localCutClass N S.val y
  let CY := localCutClass C S.val y
  let A := CY.filter fun T => T.val = insert y S.val
  let P := CY.filter fun T => T.val ≠ insert y S.val
  let E : Finset (Fin m) := Finset.univ.filter fun i =>
    ∃ T ∈ L, T.val = insert y (mappedArc e i (m - 1))
  have hvis : ∀ i ∈ E, Visible H (insert y (mappedArc e i (m - 1))) := by
    intro i hi
    obtain ⟨T, _, he⟩ := (Finset.mem_filter.mp hi).2
    rw [← he]
    exact T.property
  have hstart : ∀ i (hi : i ∈ E),
      CutReach (reconfiguration H) C s ⟨insert y (mappedArc e i (m - 1)), hvis i hi⟩ ∨
      (⟨insert y (mappedArc e i (m - 1)), hvis i hi⟩ : Configuration H) ∈ C := by
    intro i hi
    obtain ⟨T, hTL, he⟩ := (Finset.mem_filter.mp hi).2
    have hTN := (Finset.mem_filter.mp hTL).1
    have hAdj := (SimpleGraph.mem_neighborFinset _ _ _).mp hTN
    have hEq : T = ⟨insert y (mappedArc e i (m - 1)), hvis i hi⟩ := Subtype.ext he
    by_cases hTC : T ∈ C
    · exact Or.inr (hEq ▸ hTC)
    · exact Or.inl (hEq ▸ cutReach_step hs hAdj hTC)
  have hEbound := cyclic_outside_cut_bound H e (by omega) hy C s E hvis hstart
    (fun T hT _ hr => by have := hlow T hr; omega)
  have hPEq : P = C.filter fun T => y ∈ T.val ∧ T.val ⊆ insert y (Finset.univ.map e) ∧
      T.val ≠ insert y (Finset.univ.map e) := by
    ext T
    simp only [P, CY, S, localCutClass, Finset.mem_filter, and_assoc]
  rw [← hPEq] at hEbound
  let g : E → Configuration H := fun i =>
    ⟨insert y (mappedArc e i.val (m - 1)), hvis i.val i.property⟩
  have hcover : L ⊆ A ∪ Finset.univ.image g := by
    intro T hTL
    have hTN := (Finset.mem_filter.mp hTL).1
    have hlocal := (Finset.mem_filter.mp hTL).2
    have hAdj : MixedMove H S.val T.val := (SimpleGraph.mem_neighborFinset _ _ _).mp hTN
    by_cases hAdd : T.val = insert y S.val
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨?_, hlocal⟩, hAdd⟩
      by_contra hTC
      have hbig := hmax T (cutReach_step hs hAdj hTC)
      have hcard : T.val.card = m + 1 := by
        rw [hAdd, Finset.card_insert_of_notMem hy]
        simp [S]
      omega
    · apply Finset.mem_union_right
      rcases hAdj.2 with htar | ⟨x, z, hx, hz, _⟩
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp htar
        have hya : y = a := by
          have hymem : y ∈ S.val ∆ T.val := Finset.mem_symmDiff.mpr (Or.inr ⟨hlocal.1, hy⟩)
          simpa [ha] using hymem
        have he : T.val = insert y S.val := by
          apply Finset.Subset.antisymm hlocal.2
          apply Finset.insert_subset_iff.mpr
          refine ⟨hlocal.1, ?_⟩
          intro q hqS
          by_contra hqT
          have hqsy : q ∈ S.val ∆ T.val := Finset.mem_symmDiff.mpr (Or.inl ⟨hqS, hqT⟩)
          have hqy : q = y := by simpa only [ha, Finset.mem_singleton, ← hya] using hqsy
          exact hy (hqy ▸ hqS)
        exact (hAdd he).elim
      · have hyz : y = z := by
          have hymem : y ∈ T.val \ S.val := Finset.mem_sdiff.mpr ⟨hlocal.1, hy⟩
          simpa [hz] using hymem
        subst z
        have hxmem : x ∈ S.val := (Finset.mem_sdiff.mp (by rw [hx]; simp)).1
        obtain ⟨j, _, hej⟩ := Finset.mem_map.mp hxmem
        obtain ⟨i, hi⟩ := Finite.surjective_of_injective cyclicPred_injective j
        have hcoatom : mappedArc e i (m - 1) = S.val.erase x := by
          simp only [mappedArc, cyclicArc_coatom, Finset.map_erase]
          rw [hi, hej]
        have hxnotT : x ∉ T.val :=
          (Finset.mem_sdiff.mp (show x ∈ S.val \ T.val by rw [hx]; simp)).2
        have he : T.val = insert y (S.val.erase x) := by
          ext q
          constructor
          · intro hqT
            rcases Finset.mem_insert.mp (hlocal.2 hqT) with hqy | hqS
            · exact Finset.mem_insert.mpr (Or.inl hqy)
            · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr
                ⟨fun hqx => hxnotT (hqx ▸ hqT), hqS⟩))
          · intro hq
            rcases Finset.mem_insert.mp hq with rfl | hq
            · exact hlocal.1
            · obtain ⟨hqx, hqS⟩ := Finset.mem_erase.mp hq
              by_contra hqT
              have hqdiff : q ∈ S.val \ T.val := Finset.mem_sdiff.mpr ⟨hqS, hqT⟩
              exact hqx (by simpa only [hx, Finset.mem_singleton] using hqdiff)
        have hiE : i ∈ E := Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, T, hTL, by rw [hcoatom]; exact he⟩
        apply Finset.mem_image.mpr
        refine ⟨⟨i, hiE⟩, Finset.mem_univ _, Subtype.ext ?_⟩
        change insert y (mappedArc e i (m - 1)) = T.val
        rw [hcoatom]
        exact he.symm
  have hcard := (Finset.card_le_card hcover).trans (Finset.card_union_le _ _)
  have hg : (Finset.univ.image g).card ≤ E.card := by
    simpa using (Finset.card_image_le (s := Finset.univ) (f := g))
  have hpartition : A.card + P.card = CY.card := by
    exact Finset.card_filter_add_card_filter_not (s := CY) (fun T => T.val = insert y S.val)
  change L.card ≤ CY.card
  exact hcard.trans (by omega)

private theorem max_high_rank_degree {V : Type*} [Fintype V] [DecidableEq V] {m : ℕ}
    (H : SimpleGraph V) (e : Fin m ↪ V) (hm : 3 ≤ m)
    (hS : Visible H (Finset.univ.map e)) (C : Finset (Configuration H)) (s : Configuration H)
    (hs : CutReach (reconfiguration H) C s ⟨Finset.univ.map e, hS⟩)
    (hlow : ∀ T, CutReach (reconfiguration H) C s T → 3 ≤ T.val.card)
    (hmax : ∀ T, CutReach (reconfiguration H) C s T → T.val.card ≤ m) :
    (reconfiguration H).degree ⟨Finset.univ.map e, hS⟩ ≤ C.card := by
  classical
  have hinner := cyclic_internal_cut_bound H e (by omega : 2 ≤ m) hS C s hs
    (fun T hr => by have := hlow T hr; omega)
  have hY : Disjoint (Finset.univ \ Finset.univ.map e) (Finset.univ.map e) := Finset.sdiff_disjoint
  have hbudget := joint_cut_budget C (Finset.univ.map e) _ hY ∅ (by simp) (by simp) (by simp)
  have hlocal : (∑ y ∈ Finset.univ \ Finset.univ.map e,
      (localCutClass ((reconfiguration H).neighborFinset ⟨Finset.univ.map e, hS⟩)
        (Finset.univ.map e) y).card) ≤
      ∑ y ∈ Finset.univ \ Finset.univ.map e, (localCutClass C (Finset.univ.map e) y).card := by
    apply Finset.sum_le_sum
    intro y hy
    exact cyclic_local_cut_bound H e hm hS C s hs hlow hmax (Finset.mem_sdiff.mp hy).2
  have hdegree := degree_by_label_classes H ⟨Finset.univ.map e, hS⟩
  simp only [Finset.card_map, Finset.card_univ, Fintype.card_fin] at hdegree
  simp only [Finset.card_empty, Nat.add_zero] at hbudget
  omega

theorem high_rank_component {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (C : Finset (Configuration H)) (s : Configuration H) (hs : s ∉ C)
    (hlow : ∀ T, CutReach (reconfiguration H) C s T → 3 ≤ T.val.card) :
    ∃ S, CutReach (reconfiguration H) C s S ∧ (reconfiguration H).degree S ≤ C.card := by
  classical
  let E : Set (Configuration H) := {T | CutReach (reconfiguration H) C s T}
  have hE : E.Nonempty := ⟨s, hs, hs, SimpleGraph.Reachable.refl _⟩
  obtain ⟨S, hS, hmax⟩ := Set.exists_max_image E (fun T => T.val.card) (Set.toFinite E) hE
  let e : Fin S.val.card ↪ V :=
    ⟨fun i => (S.val.equivFin.symm i).val,
      fun i j h => S.val.equivFin.symm.injective (Subtype.ext h)⟩
  have hlabel : Finset.univ.map e = S.val := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hz
      exact (S.val.equivFin.symm i).property
    · intro hz
      refine Finset.mem_map.mpr ⟨S.val.equivFin ⟨z, hz⟩, Finset.mem_univ _, ?_⟩
      change ((S.val.equivFin.symm (S.val.equivFin ⟨z, hz⟩)).val) = z
      rw [Equiv.symm_apply_apply]
  have hVis : Visible H (Finset.univ.map e) := by rw [hlabel]; exact S.property
  have hEq : (⟨Finset.univ.map e, hVis⟩ : Configuration H) = S := Subtype.ext hlabel
  have hbound := max_high_rank_degree H e (hlow S hS) hVis C s
    (by rw [hEq]; exact hS) hlow (fun T hr => hmax T hr)
  rw [hEq] at hbound
  exact ⟨S, hS, hbound⟩

end D5.S3.Combinatorics.Graph.MutualVisibility
