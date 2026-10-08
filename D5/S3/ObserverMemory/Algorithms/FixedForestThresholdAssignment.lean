/- GID: D5/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/Algorithms/FixedForestThresholdAssignment
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: One descending assignment attains all fixed-forest thresholds. -/

import D5.S3.ObserverMemory.Algorithms.FixedForestOriginalImplementation
import Mathlib.Data.Fin.Tuple.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity

open StationaryUnitControl FixedForestTargetInventory FixedForestSlotGraph
attribute [local instance] Classical.propDecidable

variable {P h ell : Nat} {Node : Type} [Fintype Node] [DecidableEq Node]
variable {hP : 1 < P} (F : PhysicalForest P h ell Node hP) (R : Prescribed F)

namespace Descending
variable {D S : Type} [Fintype D] [Fintype S]

noncomputable def order (a : D → Nat) : Fin (Fintype.card D) ≃ D :=
  (Tuple.sort (α := OrderDual Nat)
    (fun i => (a ((Fintype.equivFin D).symm i) : OrderDual Nat))).trans
    (Fintype.equivFin D).symm

theorem antitone (a : D → Nat) : Antitone (a ∘ order a) := by
  intro i j hij
  exact (Tuple.monotone_sort (α := OrderDual Nat)
    (fun i => (a ((Fintype.equivFin D).symm i) : OrderDual Nat))) hij

noncomputable def count (a : D → Nat) (k : Nat) : Nat :=
  (Finset.univ.filter (fun d => k ≤ a d)).card

theorem count_order (a : D → Nat) (k : Nat) :
    count (a ∘ order a) k = count a k := by
  classical
  unfold count
  exact Finset.card_equiv (order a) (by simp)

theorem rank (a : D → Nat) (k : Nat) (i : Fin (Fintype.card D)) :
    k ≤ a (order a i) ↔ i.val < count a k := by
  rw [← count_order a k]
  exact (Tuple.lt_card_ge_iff_apply_ge_of_antitone (antitone a)).symm

noncomputable def map (a : D → Nat) (b : S → Nat)
    (h : Fintype.card D ≤ Fintype.card S) (d : D) : S :=
  order b (Fin.castLE h ((order a).symm d))

theorem injective (a : D → Nat) (b : S → Nat)
    (h : Fintype.card D ≤ Fintype.card S) : Function.Injective (map a b h) :=
  (order b).injective.comp ((Fin.castLE_injective h).comp (order a).symm.injective)

/-- The same descending map works for every threshold, including ties. -/
theorem increment_rank (a : D → Nat) (b : S → Nat)
    (h : Fintype.card D ≤ Fintype.card S) (k : Nat) (i : Fin (Fintype.card D)) :
    (k ≤ a (order a i) ∧ b (map a b h (order a i)) < k) ↔
      count b k < i.val + 1 ∧ i.val + 1 ≤ count a k := by
  have ha := rank a k i
  have hb := rank b k (Fin.castLE h i)
  simp only [map, Equiv.symm_apply_apply] at hb ⊢
  change (k ≤ b (order b (Fin.castLE h i))) ↔ i.val < count b k at hb
  change (k ≤ a (order a i) ∧ b (order b (Fin.castLE h i)) < k) ↔ _
  omega

private theorem interval_card (n a b : Nat) (ha : a ≤ n) :
    (Finset.univ.filter (fun i : Fin n => b < i.val + 1 ∧ i.val + 1 ≤ a)).card = a - b := by
  classical
  rw [← Nat.card_Ico b a]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_Ico.mpr (by omega)
  · intro i _ j _ he
    exact Fin.ext he
  · intro j hj
    have hh := Finset.mem_Ico.mp hj
    exact ⟨⟨j, by omega⟩, by simp; omega, rfl⟩

theorem simultaneous (a : D → Nat) (b : S → Nat)
    (h : Fintype.card D ≤ Fintype.card S) (k : Nat) :
    (Finset.univ.filter (fun d => k ≤ a d ∧ b (map a b h d) < k)).card =
      count a k - count b k := by
  classical
  have card := Finset.card_equiv (order a)
    (s := Finset.univ.filter (fun i : Fin (Fintype.card D) =>
      count b k < i.val + 1 ∧ i.val + 1 ≤ count a k))
    (t := Finset.univ.filter (fun d => k ≤ a d ∧ b (map a b h d) < k))
    (by intro i; simp only [Finset.mem_filter, Finset.mem_univ, true_and];
        exact (increment_rank a b h k i).symm)
  rw [← card]
  exact interval_card _ _ _ (Finset.card_filter_le _ _)

/-- Every injection pays at least the high-demand deficit. -/
theorem lower (a : D → Nat) (b : S → Nat) (f : D → S)
    (hf : Function.Injective f) (k : Nat) :
    count a k - count b k ≤
      (Finset.univ.filter (fun d => k ≤ a d ∧ b (f d) < k)).card := by
  classical
  let high := Finset.univ.filter (fun d => k ≤ a d)
  let good := high.filter (fun d => k ≤ b (f d))
  let bad := high.filter (fun d => ¬ k ≤ b (f d))
  have partition : good.card + bad.card = high.card :=
    Finset.card_filter_add_card_filter_not (s := high) _
  have bound : good.card ≤ count b k := by
    rw [← Finset.card_image_of_injective good hf]
    apply Finset.card_le_card
    intro s hs
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hs
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hd).2⟩
  have badEq : bad = Finset.univ.filter (fun d => k ≤ a d ∧ b (f d) < k) := by
    ext d; simp [bad, high]
  rw [badEq] at partition
  change count a k - count b k ≤ _
  change good.card + _ = count a k at partition
  omega
end Descending

/-- The original ordinary demands and spare slots are partitioned by absolute digit. -/
abbrev ColorDemand (c : Fin 3) :=
  {d : Ordinary F R // F.color (demandChild F R d) = c}
abbrev ColorSlot (c : Fin 3) :=
  {s : SpareSlot (e := 0) F R // s.val.2 = c}

noncomputable instance colorDemandFintype (c : Fin 3) : Fintype (ColorDemand F R c) :=
  inferInstance
noncomputable instance colorSlotFintype (c : Fin 3) : Fintype (ColorSlot F R c) :=
  inferInstance

noncomputable def A (c : Fin 3) (k : Nat) : Nat :=
  Descending.count (fun d : ColorDemand F R c => F.delay d.val.val) k
noncomputable def B (c : Fin 3) (k : Nat) : Nat :=
  Descending.count (fun s : ColorSlot F R c => baseline F R s.val.val.1) k

/-- Surplus slots remain in each color carrier; only the first n demand ranks are used. -/
noncomputable def sortedEmbedding
    (ha : ∀ c, Fintype.card (ColorDemand F R c) ≤ Fintype.card (ColorSlot F R c)) :
    Ordinary F R ↪ SpareSlot (e := 0) F R := by
  let f : (Σ c, ColorDemand F R c) → Σ c, ColorSlot F R c := fun d =>
    ⟨d.1, Descending.map (fun x => F.delay x.val.val)
      (fun s => baseline F R s.val.val.1) (ha d.1) d.2⟩
  have hf : Function.Injective f := by
    rintro ⟨c, d⟩ ⟨c', d'⟩ he
    have hc : c = c' := congrArg Sigma.fst he
    subst c'
    have hd := eq_of_heq (Sigma.mk.inj_iff.mp he).2
    exact congrArg (Sigma.mk c) (Descending.injective
      (fun x : ColorDemand F R c => F.delay x.val.val)
      (fun s : ColorSlot F R c => baseline F R s.val.val.1) (ha c) hd)
  exact ((Equiv.sigmaFiberEquiv
    (fun d : Ordinary F R => F.color (demandChild F R d))).symm.toEmbedding.trans
    ⟨f, hf⟩).trans (Equiv.sigmaFiberEquiv (fun s : SpareSlot (e := 0) F R => s.val.2)).toEmbedding

noncomputable def sortedAssignment
    (ha : ∀ c, Fintype.card (ColorDemand F R c) ≤ Fintype.card (ColorSlot F R c)) :
    Assignment (e := 0) F R where
  slot := sortedEmbedding F R ha
  injective := (sortedEmbedding F R ha).injective
  same_digit d := (Descending.map
    (fun x : ColorDemand F R (F.color (demandChild F R d)) => F.delay x.val.val)
    (fun s : ColorSlot F R (F.color (demandChild F R d)) => baseline F R s.val.val.1)
    (ha _) ⟨d, rfl⟩).property
  hits_extra i := Fin.elim0 i

noncomputable def colorMap (α : Assignment (e := 0) F R) (c : Fin 3) :
    ColorDemand F R c → ColorSlot F R c := fun d =>
  ⟨α.slot d.val, (α.same_digit d.val).trans d.property⟩

/-- One alpha, independent of k, realizes every digit threshold deficit. -/
theorem sorted_thresholds
    (ha : ∀ c, Fintype.card (ColorDemand F R c) ≤ Fintype.card (ColorSlot F R c))
    (c : Fin 3) (k : Nat) :
    (Finset.univ.filter (fun d : ColorDemand F R c =>
      k ≤ F.delay d.val.val ∧
      baseline F R ((sortedAssignment F R ha).slot d.val).val.1 < k)).card =
      A F R c k - B F R c k := by
  have hh := Descending.simultaneous
    (fun d : ColorDemand F R c => F.delay d.val.val)
    (fun s : ColorSlot F R c => baseline F R s.val.val.1) (ha c) k
  have hm (d : ColorDemand F R c) :
      (sortedAssignment F R ha).slot d.val =
        (Descending.map (fun x : ColorDemand F R c => F.delay x.val.val)
          (fun s : ColorSlot F R c => baseline F R s.val.val.1) (ha c) d).val := by
    rcases d with ⟨d, rfl⟩
    rfl
  simpa only [hm, A, B] using hh

/-- The lower bound holds for every original injection, not only the sorted map. -/
theorem arbitrary_threshold_lower (α : Assignment (e := 0) F R) (c : Fin 3) (k : Nat) :
    A F R c k - B F R c k ≤
      (Finset.univ.filter (fun d : ColorDemand F R c =>
        k ≤ F.delay d.val.val ∧ baseline F R (α.slot d.val).val.1 < k)).card := by
  exact Descending.lower _ _ (colorMap F R α c) (by
    intro d f he
    exact Subtype.ext (α.injective (congrArg Subtype.val he))) k

/-- With no extras, a target has at most one spare absolute digit. -/
theorem spare_target_injective :
    Function.Injective (fun s : SpareSlot (e := 0) F R => s.val.1) := by
  intro s t he
  have hcard : (Finset.univ \ occupied F R s.val.1).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    have hc := occupied_counts (e := 0) F R s.val.1
    have size : (Finset.univ : Finset (Fin 3)).card = 3 := by simp
    rw [size]
    cases hq : s.val.1 with
    | inl b =>
      rw [hq] at hc
      change (occupied F R (.inl b)).card = (if b.val = R.A then 3 else 2) at hc
      split_ifs at hc <;> omega
    | inr q => cases q with
      | inl u =>
        rw [hq] at hc
        change (occupied F R (.inr (.inl u))).card = 2 at hc
        omega
      | inr i => exact Fin.elim0 i
  apply Subtype.ext
  apply Prod.ext he
  apply Finset.card_le_one.mp hcard
  · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, occupied,
      Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    exact s.property
  · simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, occupied,
      Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
    intro n hn
    exact t.property n (by simpa only [he] using hn)

theorem baseline_positive (q : Target (e := 0) F R) : 0 < baseline F R q := by
  cases q with
  | inl b =>
    have hn : F.Internal b.val := Finset.card_pos.mp (by rw [b.property.1]; omega)
    have bound := binary_baseline (e := 0) F R b.val b.property.1
    have target : binaryTarget (e := 0) F R b.val b.property.1 = .inl b := by
      simp only [binaryTarget, dif_neg b.property.2]
    rw [target] at bound
    exact lt_of_lt_of_le (internal_positive F hn) bound
  | inr q => cases q with
    | inl u => exact internal_positive F (Finset.card_pos.mp (by rw [R.H1_unary]; omega))
    | inr i => exact Fin.elim0 i

theorem counts_one (c : Fin 3) :
    A F R c 1 = Fintype.card (ColorDemand F R c) ∧
    B F R c 1 = Fintype.card (ColorSlot F R c) := by
  constructor
  · unfold A Descending.count
    have all : (Finset.univ.filter (fun d : ColorDemand F R c => 1 ≤ F.delay d.val.val)) =
        Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro d _
      exact internal_positive F (ordinary_internal F R d.val)
    rw [all]; simp
  · unfold B Descending.count
    have all : (Finset.univ.filter (fun s : ColorSlot F R c =>
        1 ≤ baseline F R s.val.val.1)) = Finset.univ := by
      apply Finset.filter_eq_self.mpr
      intro s _
      exact baseline_positive F R s.val.val.1
    rw [all]; simp

theorem assignment_e0_iff : Nonempty (Assignment (e := 0) F R) ↔
    ∀ c, A F R c 1 ≤ B F R c 1 := by
  constructor
  · rintro ⟨α⟩ c
    rw [(counts_one F R c).1, (counts_one F R c).2]
    exact Fintype.card_le_of_injective (colorMap F R α c) (by
      intro d f he
      exact Subtype.ext (α.injective (congrArg Subtype.val he)))
  · intro ha
    exact ⟨sortedAssignment F R (by
      intro c; simpa only [(counts_one F R c).1, (counts_one F R c).2] using ha c)⟩

/-- The finite cutoff is the actual maximum of source literal requests and baselines. -/
noncomputable def thresholdMax : Nat :=
  max (Finset.univ.sup (fun d : Ordinary F R => F.delay d.val))
    (Finset.univ.sup (baseline (e := 0) F R))

noncomputable def E0 : Nat := ∑ q : Target (e := 0) F R, (baseline F R q - 1)
noncomputable def thresholdExcess : Nat :=
  E0 F R + ∑ c : Fin 3, ∑ k ∈ Finset.Icc 2 (thresholdMax F R), (A F R c k - B F R c k)

theorem thresholds_vanish (k : Nat) (hk : thresholdMax F R < k) (c : Fin 3) :
    A F R c k = 0 ∧ B F R c k = 0 := by
  have demand (d : Ordinary F R) : F.delay d.val ≤ thresholdMax F R :=
    by
      unfold thresholdMax
      exact le_trans (Finset.le_sup (s := Finset.univ)
        (f := fun x : Ordinary F R => F.delay x.val) (Finset.mem_univ d))
        (le_max_left _ _)
  have slot (s : SpareSlot (e := 0) F R) : baseline F R s.val.1 ≤ thresholdMax F R :=
    by
      unfold thresholdMax
      exact le_trans (Finset.le_sup (s := Finset.univ)
        (f := baseline (e := 0) F R) (Finset.mem_univ s.val.1)) (le_max_right _ _)
  constructor
  · unfold A Descending.count
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro d hd
    have high := (Finset.mem_filter.mp hd).2
    change k ≤ F.delay d.val.val at high
    have bound := demand d.val
    omega
  · unfold B Descending.count
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    have high := (Finset.mem_filter.mp hs).2
    change k ≤ baseline F R s.val.val.1 at high
    have bound := slot s.val
    omega

private theorem layer (a b U : Nat) (hb : 1 ≤ b) (ha : a ≤ U) :
    a - b = ∑ k ∈ Finset.Icc 2 U, if b < k ∧ k ≤ a then 1 else 0 := by
  have sets : (Finset.Icc 2 U).filter (fun k => b < k ∧ k ≤ a) =
      Finset.Ico (b + 1) (a + 1) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ico]
    omega
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, smul_eq_mul, mul_one, sets, Nat.card_Ico]
  omega

/-- Add colors only after proving that no target can receive two ordinary demands. -/
theorem tail_cost_split (α : Assignment (e := 0) F R) :
    (∑ q : Target (e := 0) F R, (L F R α q - 1)) =
      E0 F R + ∑ d : Ordinary F R,
        (F.delay d.val - baseline F R (α.slot d).val.1) := by
  have inj : Function.Injective (fun d => (α.slot d).val.1) :=
    (spare_target_injective F R).comp α.injective
  have atTarget (q : Target (e := 0) F R) :
      L F R α q - 1 = baseline F R q - 1 +
        ∑ d : Ordinary F R, if (α.slot d).val.1 = q then
          F.delay d.val - baseline F R q else 0 := by
    have positive := baseline_positive F R q
    by_cases hit : ∃ d, (α.slot d).val.1 = q
    · obtain ⟨d, hd⟩ := hit
      have unique (f : Ordinary F R) : (α.slot f).val.1 = q ↔ f = d :=
        ⟨fun he => inj (he.trans hd.symm), fun he => he ▸ hd⟩
      have supEq : (Finset.univ.sup (fun f : Ordinary F R =>
          if (α.slot f).val.1 = q then F.delay f.val else 0)) = F.delay d.val := by
        apply le_antisymm
        · apply Finset.sup_le
          intro f _
          split_ifs with hf
          · exact (inj (hf.trans hd.symm)) ▸ le_refl _
          · exact Nat.zero_le _
        · exact Finset.le_sup_of_le (Finset.mem_univ d) (by simp [hd])
      unfold L
      rw [supEq]
      simp only [unique, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      omega
    · have no (d : Ordinary F R) : (α.slot d).val.1 ≠ q := fun he => hit ⟨d, he⟩
      simp [L, no]
  simp_rw [atTarget]
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  unfold E0
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  simp [eq_comm]

/-- Literal increases equal the finite sum of the original threshold crossings. -/
theorem tail_cost_layers (α : Assignment (e := 0) F R) :
    (∑ q : Target (e := 0) F R, (L F R α q - 1)) = E0 F R +
      ∑ c : Fin 3, ∑ k ∈ Finset.Icc 2 (thresholdMax F R),
        (Finset.univ.filter (fun d : ColorDemand F R c =>
          k ≤ F.delay d.val.val ∧ baseline F R (α.slot d.val).val.1 < k)).card := by
  rw [tail_cost_split]
  have colors := (Equiv.sigmaFiberEquiv
    (fun d : Ordinary F R => F.color (demandChild F R d))).sum_comp
    (fun d => F.delay d.val - baseline F R (α.slot d).val.1)
  rw [← colors, Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro c _
  change (∑ d : ColorDemand F R c,
    (F.delay d.val.val - baseline F R (α.slot d.val).val.1)) = _
  have each (d : ColorDemand F R c) :
      F.delay d.val.val - baseline F R (α.slot d.val).val.1 =
        ∑ k ∈ Finset.Icc 2 (thresholdMax F R), if
          k ≤ F.delay d.val.val ∧ baseline F R (α.slot d.val).val.1 < k then 1 else 0 := by
    simpa only [and_comm] using layer (F.delay d.val.val)
      (baseline F R (α.slot d.val).val.1) (thresholdMax F R)
      (baseline_positive F R _) (by
        unfold thresholdMax
        exact le_trans (Finset.le_sup (s := Finset.univ)
          (f := fun x : Ordinary F R => F.delay x.val) (Finset.mem_univ d.val))
          (le_max_left _ _))
  simp_rw [each]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [← Finset.sum_filter]
  simp

/-- The common descending assignment minimizes the same joint-tail objective. -/
theorem sorted_cost
    (ha : ∀ c, Fintype.card (ColorDemand F R c) ≤ Fintype.card (ColorSlot F R c)) :
    (∑ q : Target (e := 0) F R, (L F R (sortedAssignment F R ha) q - 1)) =
      thresholdExcess F R ∧
    ∀ β : Assignment (e := 0) F R, thresholdExcess F R ≤
      ∑ q : Target (e := 0) F R, (L F R β q - 1) := by
  constructor
  · rw [tail_cost_layers]
    simp_rw [sorted_thresholds]
    rfl
  · intro β
    rw [tail_cost_layers]
    unfold thresholdExcess
    apply Nat.add_le_add_left
    apply Finset.sum_le_sum
    intro c _
    apply Finset.sum_le_sum
    intro k _
    exact arbitrary_threshold_lower F R β c k

end D5.S3.ObserverMemory.Algorithms.FixedForestUnitCapacity
