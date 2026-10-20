/- GID: D5/S3/Geometry/Metric/VariationPrimitive
   generality: G
   mirror-B: D5/B/S3/Geometry/Metric/VariationPrimitive
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.MeasureTheory.Function.AbsolutelyContinuous, mathlib/module/Mathlib.Topology.EMetricSpace.VariationOnFromTo]
   utility: none
   digest: Absolute continuity passes to accumulated metric variation with exact interval increments. -/

import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Tactic

/-! Absolute continuity of accumulated metric variation, with exact increments. -/

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ENNReal

namespace Original172

/-- Metric generalization of the partition proof at mathlib 56a0058, AbsolutelyContinuous.lean:358. -/
theorem metric_AC_boundedVariationOn {Y : Type*} [PseudoMetricSpace Y]
    {f : ℝ → Y} {a b : ℝ} (hf : AbsolutelyContinuousOnInterval f a b) :
    BoundedVariationOn f (uIcc a b) := by
  classical
  -- We may assume wlog that `a ≤ b`.
  wlog hab₀ : a ≤ b generalizing a b
  · specialize @this b a hf.symm (by linarith)
    rwa [uIcc_comm]
  rw [uIcc_of_le hab₀]
  -- Split the cases `a = b` (which is trivial) and `a < b`.
  rcases hab₀.eq_or_lt with rfl | hab
  · simp [BoundedVariationOn]
  -- Now remains the case `a < b`.
  -- Use the `ε`-`δ` definition of AC to get a `δ > 0` such that whenever a finite set of disjoint
  --   intervals `uIoc (a i) (b i)`, `i < n` have total length `< δ` and `a i, b i` are all in
  --  `[a, b]`, we have `∑ i ∈ range n, dist (f (a i)) (f (b i)) < 1`.
  rw [absolutelyContinuousOnInterval_iff] at hf
  obtain ⟨δ, hδ₁, hδ₂⟩ := hf 1 (by linarith)
  have hab₁ : 0 < b - a := by linarith
  -- Split `[a, b]` into subintervals `[a + i * δ', a + (i + 1) * δ']` for `i = 0, ..., n`, where
  --   `a + (n + 1) * δ' = b` and `δ' < δ`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (div_pos hδ₁ hab₁)
  set δ' := (b - a) / (n + 1)
  have hδ₃ : δ' < δ := by
    dsimp only [δ']
    convert mul_lt_mul_of_pos_right hn hab₁ using 1 <;> field
  have h_mono : Monotone fun (i : ℕ) ↦ a + ↑i * δ' := by
    apply Monotone.const_add
    apply Monotone.mul_const Nat.mono_cast
    simp only [δ']
    refine div_nonneg ?_ ?_ <;> linarith
  -- The variation of `f` on `[a, b]` is the sum of the variations on these subintervals.
  have v_sum : eVariationOn f (Icc a b) =
      ∑ i ∈ Finset.range (n + 1), eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) := by
    convert! eVariationOn.sum' f (I := fun i ↦ a + i * δ') h_mono |>.symm
    · simp
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field
    · norm_cast
  -- The variation of `f` on any subinterval `[x, y]` of `[a, b]` of length `< δ` is `≤ 1`.
  have v_each (x y : ℝ) (_ : a ≤ x) (_ : x ≤ y) (_ : y < x + δ) (_ : y ≤ b) :
      eVariationOn f (Icc x y) ≤ 1 := by
    simp only [eVariationOn, iSup_le_iff]
    intro p
    obtain ⟨hp₁, hp₂⟩ := p.2.property
    -- Focus on a partition `p` of `[x, y]` and show its variation with `f` is `≤ 1`.
    have vf : ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) < 1 := by
      apply hδ₂ (p.1, (fun i ↦ (p.2.val i, p.2.val (i + 1))))
      · constructor
        · have : Icc x y ⊆ uIcc a b := by rw [uIcc_of_le hab₀]; gcongr
          intro i hi
          constructor <;> exact this (hp₂ _)
        · rw [PairwiseDisjoint]
          convert! hp₁.pairwise_disjoint_on_Ioc_succ.set_pairwise (Finset.range p.1) using 3
          rw [uIoc_of_le (hp₁ (by lia)), Nat.succ_eq_succ]
      · suffices p.2.val p.1 - p.2.val 0 < δ by
          convert this
          rw [← Finset.sum_range_sub]
          congr; ext i
          rw [dist_comm, Real.dist_eq, abs_eq_self.mpr]
          linarith [@hp₁ i (i + 1) (by lia)]
        linarith [mem_Icc.mp (hp₂ p.1), mem_Icc.mp (hp₂ 0)]
    -- Reduce edist in the goal to dist and clear up
    have veq : (∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i))).toReal =
        ∑ i ∈ Finset.range p.1, dist (f (p.2.val i)) (f (p.2.val (i + 1))) := by
      rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
      simp_rw [← dist_edist]; congr; ext i; nth_rw 1 [dist_comm]
    have not_top : ∑ i ∈ Finset.range p.1, edist (f (p.2.val (i + 1))) (f (p.2.val i)) ≠ ⊤ := by
      simp [edist_ne_top]
    rw [← ENNReal.ofReal_toReal not_top]
    convert ENNReal.ofReal_le_ofReal (veq.symm ▸ vf.le)
    simp
  -- Reduce to goal that the variation of `f` on each of these subintervals is finite.
  simp only [BoundedVariationOn, v_sum, ne_eq, ENNReal.sum_eq_top, Finset.mem_range, not_exists,
    not_and]
  intro i hi
  -- Reduce finiteness to `≤ 1`.
  suffices eVariationOn f (Icc (a + i * δ') (a + (i + 1) * δ')) ≤ 1 from
    fun hC ↦ by simp [hC] at this
  -- Verify that `[a + i * δ', a + (i + 1) * δ']` is indeed a subinterval of `[a, b]`
  apply v_each
  · convert h_mono (show 0 ≤ i by lia); simp
  · convert h_mono (show i ≤ i + 1 by lia); norm_cast
  · rw [add_mul, ← add_assoc]; simpa
  · convert h_mono (show i + 1 ≤ n + 1 by lia)
    · norm_cast
    · simp only [Nat.cast_add, Nat.cast_one, δ']; field

variable {X : Type*} [MetricSpace X]

private theorem ac_finite_family {z : ℝ → X} {T ε δ : ℝ}
    (h : ∀ E, E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T →
      (∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) < δ →
      (∑ i ∈ Finset.range E.1, dist (z (E.2 i).1) (z (E.2 i).2)) < ε)
    {ι : Type*} [Fintype ι] (I : ι → ℝ × ℝ)
    (hm : ∀ i, (I i).1 ∈ uIcc 0 T ∧ (I i).2 ∈ uIcc 0 T)
    (hd : Pairwise fun i j => Disjoint (uIoc (I i).1 (I i).2) (uIoc (I j).1 (I j).2))
    (hl : (∑ i, dist (I i).1 (I i).2) < δ) :
    (∑ i, dist (z (I i).1) (z (I i).2)) < ε := by
  classical
  let e := Fintype.equivFin ι
  let J : ℕ → ℝ × ℝ := fun k => if hk : k < Fintype.card ι then I (e.symm ⟨k, hk⟩) else (0, 0)
  have hs (f : ℝ × ℝ → ℝ) :
      (∑ k ∈ Finset.range (Fintype.card ι), f (J k)) = ∑ i, f (I i) := by
    calc
      _ = ∑ k : Fin (Fintype.card ι), f (J k.val) := by
        rw [Fin.sum_univ_eq_sum_range (f := fun k => f (J k))]
      _ = ∑ k : Fin (Fintype.card ι), f (I (e.symm k)) := by
        apply Finset.sum_congr rfl
        intro k _
        simp [J, k.isLt]
      _ = _ := Equiv.sum_comp e.symm (fun i => f (I i))
  have hmJ : (Fintype.card ι, J) ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T := by
    constructor
    · intro k hk
      simpa [J, Finset.mem_range.mp hk] using hm (e.symm ⟨k, Finset.mem_range.mp hk⟩)
    · intro k hk l hl hkl
      have hk' : k < Fintype.card ι := Finset.mem_range.mp hk
      have hl' : l < Fintype.card ι := Finset.mem_range.mp hl
      change Disjoint (uIoc (J k).1 (J k).2) (uIoc (J l).1 (J l).2)
      have hJk : J k = I (e.symm ⟨k, hk'⟩) := dif_pos hk'
      have hJl : J l = I (e.symm ⟨l, hl'⟩) := dif_pos hl'
      rw [hJk, hJl]
      exact @hd (e.symm ⟨k, hk'⟩) (e.symm ⟨l, hl'⟩)
        (fun he => hkl (congrArg Fin.val (e.symm.injective he)))
  have hh := h (Fintype.card ι, J) hmJ (by
    change (∑ k ∈ Finset.range (Fintype.card ι), dist (J k).1 (J k).2) < δ
    rw [hs (fun v => dist v.1 v.2)]
    exact hl)
  change (∑ k ∈ Finset.range (Fintype.card ι), dist (z (J k).1) (z (J k).2)) < ε at hh
  rw [hs (fun v => dist (z v.1) (z v.2))] at hh
  exact hh

private theorem finite_sup_bound {ι : Type*} {κ : ι → Type*}
    [∀ i, Nonempty (κ i)] (s : Finset ι) (f : ∀ i, κ i → ℝ≥0∞) (r c : ℝ≥0∞)
    (h : ∀ p : ∀ i, κ i, r + ∑ i ∈ s, f i (p i) ≤ c) :
    r + ∑ i ∈ s, ⨆ j, f i j ≤ c := by
  classical
  induction s using Finset.induction_on generalizing r with
  | empty => simpa using h (fun i => Classical.choice (inferInstance : Nonempty (κ i)))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, ← add_assoc, ENNReal.add_iSup, ENNReal.iSup_add]
    apply iSup_le
    intro j
    apply ih
    intro p
    have hh := h (Function.update p a j)
    rw [Finset.sum_insert ha] at hh
    have he : (∑ i ∈ s, f i (Function.update p a j i)) = ∑ i ∈ s, f i (p i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hia : i ≠ a := by intro he; subst i; exact ha hi
      simp [Function.update, hia]
    have he' : Function.update p a j a = j := by simp [Function.update]
    rw [he', he] at hh
    simpa only [add_assoc] using hh

/-- Exact increments of the actual accumulated metric variation. -/
theorem metric_AC_variation_exact_increments {z : ℝ → X} {T : ℝ}
    (hT : 0 < T) (hz : AbsolutelyContinuousOnInterval z 0 T)
    {a b : ℝ} (ha : a ∈ Icc 0 T) (hb : b ∈ Icc 0 T) (hab : a ≤ b) :
    variationOnFromTo z (Icc 0 T) 0 b - variationOnFromTo z (Icc 0 T) 0 a =
      (eVariationOn z (Icc a b)).toReal := by
  have hBV : BoundedVariationOn z (uIcc (0 : ℝ) T) :=
    metric_AC_boundedVariationOn hz
  have hset : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT.le
  have hv : BoundedVariationOn z (Icc (0 : ℝ) T) :=
    Eq.mp (congrArg (fun s : Set ℝ => BoundedVariationOn z s) hset) hBV
  calc
    _ = variationOnFromTo z (Icc 0 T) a b :=
      variationOnFromTo.sub_right (f := z) (s := Icc 0 T) (a := 0) (b := b) (c := a)
        hv.locallyBoundedVariationOn ⟨le_rfl, hT.le⟩ hb ha
    _ = (eVariationOn z (Icc 0 T ∩ Icc a b)).toReal :=
      variationOnFromTo.eq_of_le z (Icc 0 T) hab
    _ = _ := by rw [inter_eq_right.mpr (Icc_subset_Icc ha.1 hb.2)]

private theorem refinement_bound {z : ℝ → X} {T ε δ : ℝ}
    (h : ∀ E, E ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T →
      (∑ i ∈ Finset.range E.1, dist (E.2 i).1 (E.2 i).2) < δ →
      (∑ i ∈ Finset.range E.1, dist (z (E.2 i).1) (z (E.2 i).2)) < ε)
    (n : ℕ) (I : ℕ → ℝ × ℝ)
    (hI : (n, I) ∈ AbsolutelyContinuousOnInterval.disjWithin 0 T)
    (hl : (∑ i ∈ Finset.range n, dist (I i).1 (I i).2) < δ)
    (p : ∀ i : Fin n, ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ uIcc (I i).1 (I i).2}) :
    (∑ i : Fin n, ∑ j ∈ Finset.range (p i).1,
      edist (z ((p i).2.val (j + 1))) (z ((p i).2.val j))) ≤ ENNReal.ofReal ε := by
  classical
  let R : (Σ i : Fin n, Fin (p i).1) → ℝ × ℝ :=
    fun j => ((p j.1).2.val j.2, (p j.1).2.val (j.2.val + 1))
  have hm (i : Fin n) (j : ℕ) := (p i).2.property.2 j
  have hmono (i : Fin n) : Monotone (p i).2.val := (p i).2.property.1
  have hs (i : Fin n) (j : ℕ) :
      uIoc ((p i).2.val j) ((p i).2.val (j + 1)) ⊆ uIoc (I i).1 (I i).2 := by
    intro t ht
    rw [uIoc_of_le (hmono i (Nat.le_succ j))] at ht
    exact ⟨lt_of_le_of_lt (hm i j).1 ht.1, ht.2.trans (hm i (j + 1)).2⟩
  have hRm : ∀ j, (R j).1 ∈ uIcc 0 T ∧ (R j).2 ∈ uIcc 0 T := by
    rintro ⟨i, j⟩
    have hi := hI.1 i (Finset.mem_range.mpr i.isLt)
    have h1 := hm i j
    have h2 := hm i (j.val + 1)
    dsimp [R]
    constructor <;> grind [uIcc, mem_Icc]
  have hRd : Pairwise fun j k => Disjoint (uIoc (R j).1 (R j).2) (uIoc (R k).1 (R k).2) := by
    rintro ⟨i, j⟩ ⟨i', k⟩ hjk
    by_cases hii : i = i'
    · subst i'
      have hne : j.val ≠ k.val := by
        intro he
        apply hjk
        congr
        exact Fin.ext he
      apply Set.disjoint_left.mpr
      intro t ht ht'
      change t ∈ uIoc ((p i).2.val j) ((p i).2.val (j.val + 1)) at ht
      change t ∈ uIoc ((p i).2.val k) ((p i).2.val (k.val + 1)) at ht'
      rw [uIoc_of_le (hmono i (Nat.le_succ j.val))] at ht
      rw [uIoc_of_le (hmono i (Nat.le_succ k.val))] at ht'
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hh := hmono i (show j.val + 1 ≤ k.val by omega)
        linarith [ht.2, ht'.1]
      · have hh := hmono i (show k.val + 1 ≤ j.val by omega)
        linarith [ht'.2, ht.1]
    · exact (hI.2 (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr i'.isLt)
        (fun he => hii (Fin.ext he))).mono (hs i j) (hs i' k)
  have hRl : (∑ j, dist (R j).1 (R j).2) < δ := by
    apply lt_of_le_of_lt _ hl
    rw [Fintype.sum_sigma, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_le_sum
    intro i _
    change (∑ j : Fin (p i).1, dist ((p i).2.val j) ((p i).2.val (j.val + 1))) ≤ _
    rw [Fin.sum_univ_eq_sum_range (f := fun j =>
      dist ((p i).2.val j) ((p i).2.val (j + 1)))]
    calc
      _ = ∑ j ∈ Finset.range (p i).1, ((p i).2.val (j + 1) - (p i).2.val j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr (hmono i (Nat.le_succ j)))]
        ring
      _ = (p i).2.val (p i).1 - (p i).2.val 0 := Finset.sum_range_sub _ _
      _ ≤ max (I i).1 (I i).2 - min (I i).1 (I i).2 := sub_le_sub (hm i (p i).1).2 (hm i 0).1
      _ = dist (I i).1 (I i).2 := by rw [Real.dist_eq, max_sub_min_eq_abs']
  have hh := ac_finite_family h R hRm hRd hRl
  have hn : (∑ j, edist (z (R j).2) (z (R j).1)) ≠ ⊤ := by simp [edist_ne_top]
  have he : (∑ j, edist (z (R j).2) (z (R j).1)) ≤ ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hn]
    apply ENNReal.ofReal_le_ofReal
    rw [ENNReal.toReal_sum (by simp [edist_ne_top])]
    simpa only [← dist_edist, dist_comm] using hh.le
  rw [Fintype.sum_sigma] at he
  have hconv (i : Fin n) :
      (∑ j : Fin (p i).1, edist (z ((p i).2.val (j.val + 1))) (z ((p i).2.val j.val))) =
      ∑ j ∈ Finset.range (p i).1, edist (z ((p i).2.val (j + 1))) (z ((p i).2.val j)) := by
    rw [Fin.sum_univ_eq_sum_range (f := fun j =>
      edist (z ((p i).2.val (j + 1))) (z ((p i).2.val j)))]
  change (∑ i : Fin n, ∑ j : Fin (p i).1,
    edist (z ((p i).2.val (j.val + 1))) (z ((p i).2.val j.val))) ≤ _ at he
  simpa only [hconv] using he

/-- Metric absolute continuity passes to the actual accumulated variation. -/
theorem metric_AC_implies_AC_variation_primitive {z : ℝ → X} {T : ℝ}
    (hT : 0 < T) (hz : AbsolutelyContinuousOnInterval z 0 T) :
    AbsolutelyContinuousOnInterval (variationOnFromTo z (Icc 0 T) 0) 0 T := by
  classical
  let A := variationOnFromTo z (Icc 0 T) 0
  have hBV : BoundedVariationOn z (uIcc (0 : ℝ) T) :=
    metric_AC_boundedVariationOn hz
  have hset : uIcc (0 : ℝ) T = Icc (0 : ℝ) T := uIcc_of_le hT.le
  have hv : BoundedVariationOn z (Icc (0 : ℝ) T) :=
    Eq.mp (congrArg (fun s : Set ℝ => BoundedVariationOn z s) hset) hBV
  have hd (a b : ℝ) (ha : a ∈ uIcc 0 T) (hb : b ∈ uIcc 0 T) :
      dist (A a) (A b) = (eVariationOn z (uIcc a b)).toReal := by
    rw [uIcc_of_le hT.le] at ha hb
    rcases le_total a b with hab | hba
    · rw [uIcc_of_le hab]
      have he := metric_AC_variation_exact_increments (z := z) (T := T) hT hz ha hb hab
      calc
        _ = |A b - A a| := by rw [Real.dist_eq, abs_sub_comm]
        _ = _ := by rw [show A b - A a = _ from he, abs_of_nonneg ENNReal.toReal_nonneg]
    · rw [uIcc_of_ge hba, dist_comm]
      have he := metric_AC_variation_exact_increments (z := z) (T := T) hT hz hb ha hba
      calc
        _ = |A a - A b| := by rw [Real.dist_eq, abs_sub_comm]
        _ = _ := by rw [show A a - A b = _ from he, abs_of_nonneg ENNReal.toReal_nonneg]
  rw [absolutelyContinuousOnInterval_iff]
  intro ε hε
  obtain ⟨δ, hδ, hh⟩ := (absolutelyContinuousOnInterval_iff z 0 T).mp hz (ε / 2) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  rintro ⟨n, I⟩ hI hl
  let P (i : Fin n) := ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ j, u j ∈ uIcc (I i).1 (I i).2}
  letI : ∀ i, Nonempty (P i) := fun i =>
    ⟨(0, ⟨fun _ => min (I i).1 (I i).2, monotone_const, fun _ => ⟨le_rfl, min_le_max⟩⟩)⟩
  have hs : (∑ i : Fin n, eVariationOn z (uIcc (I i).1 (I i).2)) ≤ ENNReal.ofReal (ε / 2) := by
    simpa only [zero_add, eVariationOn] using
      finite_sup_bound (κ := P) Finset.univ
        (fun i p => ∑ j ∈ Finset.range p.1, edist (z (p.2.val (j + 1))) (z (p.2.val j)))
        0 (ENNReal.ofReal (ε / 2)) (fun p => by
          simpa only [zero_add] using refinement_bound hh n I hI hl p)
  have hn (i : Fin n) : eVariationOn z (uIcc (I i).1 (I i).2) ≠ ⊤ := by
    apply hv.mono
    have hi := hI.1 i (Finset.mem_range.mpr i.isLt)
    rw [uIcc_of_le hT.le] at hi
    intro t ht
    grind [uIcc, mem_Icc]
  have hr := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hs
  rw [ENNReal.toReal_sum (fun i _ => hn i), ENNReal.toReal_ofReal (by positivity)] at hr
  have he : (∑ i ∈ Finset.range n, dist (A (I i).1) (A (I i).2)) =
      ∑ i : Fin n, (eVariationOn z (uIcc (I i).1 (I i).2)).toReal := by
    rw [Fin.sum_univ_eq_sum_range (f := fun i =>
      (eVariationOn z (uIcc (I i).1 (I i).2)).toReal)]
    apply Finset.sum_congr rfl
    intro i hi
    exact hd _ _ (hI.1 i hi).1 (hI.1 i hi).2
  change (∑ i ∈ Finset.range n, dist (A (I i).1) (A (I i).2)) < ε
  rw [he]
  linarith

end Original172
