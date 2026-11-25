/- GID: D5/S3/Combinatorics/Dice/RankingProfileRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/RankingProfileRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [lake/module/D5.S3.Combinatorics.Dice.RankingProfileFiniteGrid, mathlib/module/Mathlib.MeasureTheory.Function.Floor, mathlib/module/Mathlib.Probability.Independence.Basic]
   utility: none
   digest: An exact finite cubic criterion for six strict-order probabilities. -/

import D5.S3.Combinatorics.Dice.RankingProfileFiniteGrid
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith

/-! An exact finite criterion for the full ranking profile in Bozóki, Csató and
Temesi, *Condorcet’s nontransitive dice*, arXiv:2611.23308v1, §5, Problem 5. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.RankingProfileRealization

section Quantization

open Filter MeasureTheory Set
open scoped Topology BigOperators

private def clamp (m : ℕ) (x : ℝ) : ℝ :=
  max (-(m : ℝ)) (min (m : ℝ) x)

/-- A bounded integer quantizer whose offset identifies the role. -/
private noncomputable def Q (m : ℕ) (i : Fin 3) (x : ℝ) : ℤ :=
  3 * ⌊((m : ℝ) + 1) * clamp m x⌋ + (i.val : ℤ)

private theorem measurable_Q (m : ℕ) (i : Fin 3) : Measurable (Q m i) := by
  have hc : Measurable (clamp m) :=
    measurable_const.max (measurable_const.min measurable_id)
  have hf : Measurable (fun x : ℝ => ⌊((m : ℝ) + 1) * clamp m x⌋) :=
    (measurable_const.mul hc).floor
  exact (measurable_const.mul hf).add measurable_const

private theorem finite_range_Q (m : ℕ) (i : Fin 3) : (range (Q m i)).Finite := by
  let lower : ℤ := ⌊((m : ℝ) + 1) * -(m : ℝ)⌋
  let upper : ℤ := ⌊((m : ℝ) + 1) * (m : ℝ)⌋
  refine (Set.finite_Icc
    (a := 3 * lower + (i.val : ℤ)) (b := 3 * upper + (i.val : ℤ))).subset ?_
  rintro _ ⟨x, rfl⟩
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hs : (0 : ℝ) ≤ (m : ℝ) + 1 := by linarith
  have hlow : -(m : ℝ) ≤ clamp m x := le_max_left _ _
  have hupp : clamp m x ≤ (m : ℝ) :=
    max_le (by linarith) (min_le_left _ _)
  have hl : lower ≤ ⌊((m : ℝ) + 1) * clamp m x⌋ :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hlow hs)
  have hu : ⌊((m : ℝ) + 1) * clamp m x⌋ ≤ upper :=
    Int.floor_mono (mul_le_mul_of_nonneg_left hupp hs)
  change 3 * lower + (i.val : ℤ) ≤ Q m i x ∧ Q m i x ≤ 3 * upper + (i.val : ℤ)
  unfold Q
  omega

private theorem disjoint_range_Q (m : ℕ) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (range (Q m i)) (range (Q m j)) := by
  refine Set.disjoint_left.2 ?_
  rintro _ ⟨x, rfl⟩ ⟨y, h⟩
  apply hij
  apply Fin.ext
  have hi := i.isLt
  have hj := j.isLt
  unfold Q at h
  omega

private theorem eventually_Q_lt {x y : ℝ} (hxy : x < y) :
    ∀ᶠ m : ℕ in atTop, ∀ i j : Fin 3, Q m i x < Q m j y := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max (max |x| |y|) (1 / (y - x)))
  filter_upwards [eventually_ge_atTop N] with m hm
  have hNm : (N : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hx : |x| ≤ (m : ℝ) :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (hN.le.trans hNm)
  have hy : |y| ≤ (m : ℝ) :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (hN.le.trans hNm)
  rw [abs_le] at hx hy
  have hcx : clamp m x = x := by
    rw [clamp, min_eq_right hx.2, max_eq_right hx.1]
  have hcy : clamp m y = y := by
    rw [clamp, min_eq_right hy.2, max_eq_right hy.1]
  have hthreshold : 1 / (y - x) < (m : ℝ) :=
    ((le_max_right _ _).trans_lt hN).trans_le hNm
  have hgap : 1 < (m : ℝ) * (y - x) :=
    (div_lt_iff₀ (sub_pos.mpr hxy)).mp hthreshold
  have hsep : ((m : ℝ) + 1) * x + 1 ≤ ((m : ℝ) + 1) * y := by
    linarith [hgap]
  have hfloor : ⌊((m : ℝ) + 1) * x⌋ < ⌊((m : ℝ) + 1) * y⌋ := by
    by_contra! h
    have hcast : (⌊((m : ℝ) + 1) * y⌋ : ℝ) ≤ (⌊((m : ℝ) + 1) * x⌋ : ℝ) := by
      exact_mod_cast h
    have hxFloor := Int.floor_le (((m : ℝ) + 1) * x)
    have hyFloor := Int.lt_floor_add_one (((m : ℝ) + 1) * y)
    linarith
  intro i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Q, Q, hcx, hcy]
  omega

private theorem eventually_Q_lt_iff {x y : ℝ} (hxy : x ≠ y) (i j : Fin 3) :
    ∀ᶠ m : ℕ in atTop, Q m i x < Q m j y ↔ x < y := by
  rcases lt_or_gt_of_ne hxy with h | h
  · filter_upwards [eventually_Q_lt h] with m hm
    exact iff_of_true (hm i j) h
  · filter_upwards [eventually_Q_lt h] with m hm
    exact iff_of_false (not_lt_of_gt (hm j i)) (not_lt_of_gt h)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Fin 3 → Ω → ℝ} {i : Fin 3}

/-- The strict ranking probabilities converge for every finite measure, in particular for a
probability measure. The hypotheses require almost-sure inequality for the two adjacent pairs. -/
private theorem tendsto_measure_strict_order_Q [IsFiniteMeasure μ]
    (hX : ∀ a, Measurable (X a)) {i j k : Fin 3}
    (hij : ∀ᵐ ω ∂μ, X i ω ≠ X j ω) (hjk : ∀ᵐ ω ∂μ, X j ω ≠ X k ω) :
    Tendsto (fun m : ℕ => μ {ω | Q m j (X j ω) < Q m i (X i ω) ∧
        Q m k (X k ω) < Q m j (X j ω)}) atTop
      (𝓝 (μ {ω | X j ω < X i ω ∧ X k ω < X j ω})) := by
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop
    ((measurableSet_lt (hX j) (hX i)).inter (measurableSet_lt (hX k) (hX j))) ?_ ?_
  · intro m
    have hQ (a : Fin 3) : Measurable (fun ω => Q m a (X a ω)) :=
      (measurable_Q m a).comp (hX a)
    exact (measurableSet_lt (hQ j) (hQ i)).inter (measurableSet_lt (hQ k) (hQ j))
  · filter_upwards [hij, hjk] with ω hωij hωjk
    filter_upwards [eventually_Q_lt_iff hωij.symm j i, eventually_Q_lt_iff hωjk.symm k j]
      with m h₁ h₂
    exact and_congr h₁ h₂

private theorem tendsto_measureReal_strict_order_Q [IsFiniteMeasure μ]
    (hX : ∀ a, Measurable (X a)) {i j k : Fin 3}
    (hij : ∀ᵐ ω ∂μ, X i ω ≠ X j ω) (hjk : ∀ᵐ ω ∂μ, X j ω ≠ X k ω) :
    Tendsto (fun m : ℕ => μ.real {ω | Q m j (X j ω) < Q m i (X i ω) ∧
        Q m k (X k ω) < Q m j (X j ω)}) atTop
      (𝓝 (μ.real {ω | X j ω < X i ω ∧ X k ω < X j ω})) :=
  (ENNReal.tendsto_toReal (measure_ne_top μ _)).comp
    (tendsto_measure_strict_order_Q hX hij hjk)

/-- A common finite alphabet for the three quantized variables, ordered as a subtype of ℤ. -/
private abbrev QuantizedValue (m : ℕ) :=
  (⋃ i : Fin 3, range (Q m i) : Set ℤ)

private noncomputable instance quantizedValueFintype (m : ℕ) : Fintype (QuantizedValue m) :=
  (finite_iUnion (finite_range_Q m)).fintype

private noncomputable def finiteQ (m : ℕ) (i : Fin 3) (x : ℝ) : QuantizedValue m :=
  ⟨Q m i x, mem_iUnion.2 ⟨i, x, rfl⟩⟩

private theorem measurable_finiteQ (m : ℕ) (i : Fin 3) : Measurable (finiteQ m i) :=
  (measurable_Q m i).subtype_mk

/-- The finite joint law is the product of the three marginal pushforwards. -/
private theorem map_finiteQ_eq_pi (hX : ∀ i, Measurable (X i))
    (hInd : ProbabilityTheory.iIndepFun X μ) (m : ℕ) :
    μ.map (fun ω i => finiteQ m i (X i ω)) =
      Measure.pi (fun i => μ.map (fun ω => finiteQ m i (X i ω))) :=
  (hInd.comp (finiteQ m) (measurable_finiteQ m)).map_fun_eq_pi_map
    (fun i => ((measurable_finiteQ m i).comp (hX i)).aemeasurable)

private noncomputable def quantizedWeight (μ : Measure Ω) (X : Fin 3 → Ω → ℝ)
    (m : ℕ) (i : Fin 3) (z : QuantizedValue m) : ℝ :=
  (μ.map (fun ω => finiteQ m i (X i ω))).real {z}

private theorem quantizedWeight_eq (hX : Measurable (X i)) (m : ℕ) (z : QuantizedValue m) :
    quantizedWeight μ X m i z = μ.real {ω | Q m i (X i ω) = (z : ℤ)} := by
  simp only [quantizedWeight, measureReal_def]
  have hf : Measurable (fun ω => finiteQ m i (X i ω)) :=
    (measurable_finiteQ m i).comp hX
  rw [Measure.map_apply hf (measurableSet_singleton z)]
  congr 2
  ext ω
  exact Subtype.ext_iff

private theorem quantizedWeight_nonneg (m : ℕ) (i : Fin 3) (z : QuantizedValue m) :
    0 ≤ quantizedWeight μ X m i z :=
  measureReal_nonneg

private theorem sum_quantizedWeight [IsProbabilityMeasure μ]
    (hX : Measurable (X i)) (m : ℕ) : ∑ z, quantizedWeight μ X m i z = 1 := by
  have hf := (measurable_finiteQ m i).comp hX
  let ν := μ.map (fun ω => finiteQ m i (X i ω))
  have : IsProbabilityMeasure ν := (Measure.isProbabilityMeasure_map_iff hf.aemeasurable).2
    inferInstance
  change (∑ z, ν.real {z}) = 1
  rw [sum_measureReal_singleton]
  simp [measureReal_def]

private theorem quantizedWeight_disjoint (hX : ∀ i, Measurable (X i)) (m : ℕ)
    {i j : Fin 3} (hij : i ≠ j) (z : QuantizedValue m) :
    quantizedWeight μ X m i z = 0 ∨ quantizedWeight μ X m j z = 0 := by
  have zeroWeight (a : Fin 3) (ha : (z : ℤ) ∉ range (Q m a)) :
      quantizedWeight μ X m a z = 0 := by
    rw [quantizedWeight_eq (hX a)]
    have hempty : {ω | Q m a (X a ω) = (z : ℤ)} = ∅ :=
      eq_empty_iff_forall_notMem.2 fun ω h => ha ⟨X a ω, h⟩
    simp [hempty]
  by_cases hi : (z : ℤ) ∈ range (Q m i)
  · exact Or.inr (zeroWeight j fun hj => Set.disjoint_left.1 (disjoint_range_Q m hij) hi hj)
  · exact Or.inl (zeroWeight i hi)

/-- A quantized ordering event is the finite sum of the masses of its ranking tuples. -/
private theorem measureReal_strict_order_Q_eq_sum
    (hX : ∀ a, Measurable (X a)) (hInd : ProbabilityTheory.iIndepFun X μ)
    (m : ℕ) (i j k : Fin 3) :
    μ.real {ω | Q m j (X j ω) < Q m i (X i ω) ∧
        Q m k (X k ω) < Q m j (X j ω)} =
      ∑ r : Fin 3 → QuantizedValue m, if r j < r i ∧ r k < r j then
        ∏ a, quantizedWeight μ X m a (r a) else 0 := by
  classical
  let ν (a : Fin 3) := μ.map (fun ω => finiteQ m a (X a ω))
  let A := Finset.univ.filter
    (fun r : Fin 3 → QuantizedValue m => r j < r i ∧ r k < r j)
  have : IsProbabilityMeasure μ := hInd.isProbabilityMeasure
  have hQ (a : Fin 3) : Measurable (fun ω => finiteQ m a (X a ω)) :=
    (measurable_finiteQ m a).comp (hX a)
  have : ∀ a, IsProbabilityMeasure (ν a) := fun a =>
    (Measure.isProbabilityMeasure_map_iff (hQ a).aemeasurable).2 inferInstance
  have hf : Measurable (fun ω a => finiteQ m a (X a ω)) := measurable_pi_iff.2 hQ
  have hmass (r : Fin 3 → QuantizedValue m) :
      (Measure.pi ν).real {r} = ∏ a, quantizedWeight μ X m a (r a) := by
    simp only [measureReal_def, Measure.pi_singleton, ENNReal.toReal_prod, quantizedWeight, ν]
  calc
    _ = (μ.map (fun ω a => finiteQ m a (X a ω))).real (A : Set _) := by
      simp only [measureReal_def, Measure.map_apply hf A.finite_toSet.measurableSet]
      congr 2
      ext ω
      simp only [mem_ofPred_eq, mem_preimage, Finset.mem_coe, A, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rfl
    _ = (Measure.pi ν).real (A : Set _) := by rw [map_finiteQ_eq_pi hX hInd]
    _ = _ := by
      rw [← sum_measureReal_singleton]
      simp only [hmass, A, Finset.sum_filter]

end Quantization

section ProbabilityBridge

open Filter MeasureTheory Set ProbabilityTheory
open scoped Topology BigOperators

/-- Roles in decreasing order for XYZ, XZY, YXZ, YZX, ZXY, ZYX. -/
def rankOrder : Fin 6 → Fin 3 → Fin 3 :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![1, 2, 0], ![2, 0, 1], ![2, 1, 0]]

private def rankEvent {Ω α : Type*} [LT α] (X : Fin 3 → Ω → α) (t : Fin 6) : Set Ω :=
  {ω | X (rankOrder t 1) ω < X (rankOrder t 0) ω ∧
    X (rankOrder t 2) ω < X (rankOrder t 1) ω}

noncomputable def realRankProfile {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Fin 3 → Ω → ℝ) : Fin 6 → ℝ :=
  fun t => μ.real (rankEvent X t)

section RealVariables

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Fin 3 → Ω → ℝ}

private theorem measurableSet_rankEvent (hX : ∀ i, Measurable (X i)) (t : Fin 6) :
    MeasurableSet (rankEvent X t) :=
  (measurableSet_lt (hX _) (hX _)).inter (measurableSet_lt (hX _) (hX _))

omit [MeasurableSpace Ω] in
private theorem pairwiseDisjoint_rankEvent :
    Pairwise (fun t u => Disjoint (rankEvent X t) (rankEvent X u)) := by
  intro t u htu
  refine Set.disjoint_left.2 fun ω ht hu => ?_
  fin_cases t <;> fin_cases u <;>
    first | exact htu rfl | (simp [rankEvent, rankOrder] at ht hu
                             linarith only [ht.1, ht.2, hu.1, hu.2])

private theorem distinctThree_iff (x : Fin 3 → ℝ) :
    (∀ i j, i ≠ j → x i ≠ x j) ↔
      x 0 ≠ x 1 ∧ x 0 ≠ x 2 ∧ x 1 ≠ x 2 := by
  refine ⟨fun h => ⟨h 0 1 (by decide), h 0 2 (by decide), h 1 2 (by decide)⟩, ?_⟩
  rintro ⟨h01, h02, h12⟩ i j hij
  fin_cases i <;> fin_cases j <;>
    first | exact (hij rfl).elim | exact h01 | exact h02 | exact h12 |
      exact h01.symm | exact h02.symm | exact h12.symm

omit [MeasurableSpace Ω] in
private theorem iUnion_rankEvent :
    (⋃ t, rankEvent X t) = {ω | ∀ i j, i ≠ j → X i ω ≠ X j ω} := by
  ext ω
  rw [Set.mem_iUnion]
  change (∃ t, ω ∈ rankEvent X t) ↔ (∀ i j, i ≠ j → X i ω ≠ X j ω)
  rw [distinctThree_iff]
  constructor
  · rintro ⟨t, ht⟩
    fin_cases t <;> simp [rankEvent, rankOrder] at ht <;>
      refine ⟨?_, ?_, ?_⟩ <;> intro h <;> linarith only [ht.1, ht.2, h]
  · rintro ⟨h01, h02, h12⟩
    rcases lt_or_gt_of_ne h01 with h01 | h01 <;>
      rcases lt_or_gt_of_ne h02 with h02 | h02 <;>
      rcases lt_or_gt_of_ne h12 with h12 | h12 <;>
      first
      | solve
        | exact ⟨0, by simpa [rankEvent, rankOrder] using And.intro h01 h12⟩
        | exact ⟨1, by simpa [rankEvent, rankOrder] using And.intro h02 h12⟩
        | exact ⟨2, by simpa [rankEvent, rankOrder] using And.intro h01 h02⟩
        | exact ⟨3, by simpa [rankEvent, rankOrder] using And.intro h12 h02⟩
        | exact ⟨4, by simpa [rankEvent, rankOrder] using And.intro h02 h01⟩
        | exact ⟨5, by simpa [rankEvent, rankOrder] using And.intro h12 h01⟩

private theorem ae_distinct_of_sum_realRankProfile [IsProbabilityMeasure μ]
    (hX : ∀ i, Measurable (X i)) (hs : ∑ t, realRankProfile μ X t = 1) :
    ∀ᵐ ω ∂μ, ∀ i j, i ≠ j → X i ω ≠ X j ω := by
  have hm := MeasurableSet.iUnion (measurableSet_rankEvent hX)
  have hr : μ.real (⋃ t, rankEvent X t) = 1 :=
    (measureReal_iUnion_fintype pairwiseDisjoint_rankEvent (measurableSet_rankEvent hX)).trans hs
  have hmass : μ (⋃ t, rankEvent X t) = 1 := by
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) ENNReal.one_ne_top).1
    simpa only [← measureReal_def, ENNReal.toReal_one] using hr
  rw [iUnion_rankEvent] at hm hmass
  exact (ae_iff_measure_eq hm.nullMeasurableSet).2 (hmass.trans (measure_univ).symm)

end RealVariables

private theorem rankOrder_bijective (t : Fin 6) : Function.Bijective (rankOrder t) := by
  fin_cases t <;> decide

private noncomputable def rankPermutation (t : Fin 6) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective _ (rankOrder_bijective t)

private def tripleEquiv (α : Type*) : (Fin 3 → α) ≃ α × α × α where
  toFun r := (r 0, r 1, r 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv r := by
    funext i
    fin_cases i <;> rfl
  right_inv p := by
    rcases p with ⟨x, y, z⟩
    rfl

/-- First list the roles in ranking order, then identify a three-entry function with a triple. -/
private noncomputable def rankTupleEquiv (α : Type*) (t : Fin 6) : (Fin 3 → α) ≃ α × α × α :=
  ((rankPermutation t).symm.arrowCongr (Equiv.refl α)).trans (tripleEquiv α)

private theorem sum_rankTuples {α : Type*} [Fintype α] [LinearOrder α]
    (p : Fin 3 → α → ℝ) (t : Fin 6) :
    (∑ r : Fin 3 → α,
      if r (rankOrder t 1) < r (rankOrder t 0) ∧ r (rankOrder t 2) < r (rankOrder t 1)
      then ∏ i, p i (r i) else 0) =
    rankMass (p (rankOrder t 0)) (p (rankOrder t 1)) (p (rankOrder t 2)) := by
  classical
  let e := rankTupleEquiv α t
  let f (v : α × α × α) :=
    if v.2.2 < v.2.1 ∧ v.2.1 < v.1 then
      p (rankOrder t 0) v.1 * p (rankOrder t 1) v.2.1 * p (rankOrder t 2) v.2.2 else 0
  calc
    _ = ∑ r, f (e r) := by
      apply Finset.sum_congr rfl
      intro r _
      have hp := Equiv.prod_comp (rankPermutation t) (fun i => p i (r i))
      rw [Fin.prod_univ_three] at hp
      change p (rankOrder t 0) (r (rankOrder t 0)) *
        p (rankOrder t 1) (r (rankOrder t 1)) *
        p (rankOrder t 2) (r (rankOrder t 2)) = ∏ i, p i (r i) at hp
      change _ = if r (rankOrder t 2) < r (rankOrder t 1) ∧
          r (rankOrder t 1) < r (rankOrder t 0) then _ else 0
      by_cases h : r (rankOrder t 1) < r (rankOrder t 0) ∧ r (rankOrder t 2) < r (rankOrder t 1)
      · rw [ite_eq_left h, ite_eq_left h.symm]
        exact hp.symm
      · rw [ite_eq_right h, ite_eq_right (fun hrev => h hrev.symm)]
    _ = ∑ v, f v := e.sum_comp f
    _ = _ := by simp only [Fintype.sum_prod_type, f, rankMass]

private theorem profile_eq_rankMass {α : Type*} [Fintype α] [LinearOrder α]
    (p : Fin 3 → α → ℝ) (t : Fin 6) :
    profile (p 0) (p 1) (p 2) t =
      rankMass (p (rankOrder t 0)) (p (rankOrder t 1)) (p (rankOrder t 2)) := by
  fin_cases t <;> rfl

section Quantized

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Fin 3 → Ω → ℝ}

private theorem quantizedWeights_probability [IsProbabilityMeasure μ]
    (hX : ∀ i, Measurable (X i)) (m : ℕ) (i : Fin 3) :
    IsProbability (quantizedWeight μ X m i) :=
  ⟨quantizedWeight_nonneg m i, sum_quantizedWeight (hX i) m⟩

private theorem quantizedWeights_disjoint (hX : ∀ i, Measurable (X i)) (m : ℕ) :
    Pairwise (fun i j => Disjoint (weightSupport (quantizedWeight μ X m i))
      (weightSupport (quantizedWeight μ X m j))) := by
  intro i j hij
  refine Finset.disjoint_left.2 fun z hi hj => ?_
  rcases quantizedWeight_disjoint hX m hij z with hz | hz
  · exact (show quantizedWeight μ X m i z ≠ 0 by simpa [weightSupport] using hi) hz
  · exact (show quantizedWeight μ X m j z ≠ 0 by simpa [weightSupport] using hj) hz

private theorem quantizedProfile_eq (hX : ∀ i, Measurable (X i))
    (hInd : iIndepFun X μ) (m : ℕ) (t : Fin 6) :
    μ.real (rankEvent (fun i ω => Q m i (X i ω)) t) =
      profile (quantizedWeight μ X m 0) (quantizedWeight μ X m 1)
        (quantizedWeight μ X m 2) t := by
  rw [profile_eq_rankMass (quantizedWeight μ X m), ← sum_rankTuples]
  exact measureReal_strict_order_Q_eq_sum hX hInd m _ _ _

private theorem tendsto_quantizedProfile [IsProbabilityMeasure μ]
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hs : ∑ t, realRankProfile μ X t = 1) :
    Tendsto (fun m => profile (quantizedWeight μ X m 0) (quantizedWeight μ X m 1)
      (quantizedWeight μ X m 2)) atTop (𝓝 (realRankProfile μ X)) := by
  apply tendsto_pi_nhds.2
  intro t
  simp_rw [← quantizedProfile_eq hX hInd]
  have hd := ae_distinct_of_sum_realRankProfile hX hs
  have hij : rankOrder t 0 ≠ rankOrder t 1 := fun h =>
    (by decide : (0 : Fin 3) ≠ 1) ((rankOrder_bijective t).1 h)
  have hjk : rankOrder t 1 ≠ rankOrder t 2 := fun h =>
    (by decide : (1 : Fin 3) ≠ 2) ((rankOrder_bijective t).1 h)
  exact tendsto_measureReal_strict_order_Q hX
    (hd.mono fun _ h => h _ _ hij) (hd.mono fun _ h => h _ _ hjk)

end Quantized

section FiniteLaw

/-- The measure on the finite ordered labels with the given point masses. -/
private noncomputable def finiteWeightLaw {n : ℕ} (p : Fin n → ℝ) : Measure (Fin n) :=
  Measure.sum (fun z => ENNReal.ofReal (p z) • Measure.dirac z)

private theorem finiteWeightLaw_probability {n : ℕ} {p : Fin n → ℝ} (hp : IsProbability p) :
    IsProbabilityMeasure (finiteWeightLaw p) := by
  constructor
  simp only [finiteWeightLaw, Measure.sum_apply _ MeasurableSet.univ, tsum_fintype,
    Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hp.1 z), hp.2, ENNReal.ofReal_one]

private theorem finiteWeightLaw_singleton {n : ℕ} {p : Fin n → ℝ} (z : Fin n) :
    finiteWeightLaw p {z} = ENNReal.ofReal (p z) := by
  classical
  simp [finiteWeightLaw, Set.indicator_apply, mul_ite, eq_comm]

/-- The product of the three marginal laws on ordered labels. -/
private noncomputable def finiteProductLaw {n : ℕ} (p : Fin 3 → Fin n → ℝ) :
    Measure (Fin 3 → Fin n) :=
  Measure.pi (fun i => finiteWeightLaw (p i))

private def finiteRealCoordinate {n : ℕ} (i : Fin 3) (r : Fin 3 → Fin n) : ℝ :=
  ((r i).val : ℝ)

private theorem finiteRealCoordinate_measurable {n : ℕ} (i : Fin 3) :
    Measurable (finiteRealCoordinate (n := n) i) :=
  measurable_of_finite _

private theorem finiteProductLaw_probability {n : ℕ} {p : Fin 3 → Fin n → ℝ}
    (hp : ∀ i, IsProbability (p i)) : IsProbabilityMeasure (finiteProductLaw p) := by
  let : ∀ i, IsProbabilityMeasure (finiteWeightLaw (p i)) :=
    fun i => finiteWeightLaw_probability (hp i)
  unfold finiteProductLaw
  infer_instance

private theorem finiteRealCoordinate_iIndepFun {n : ℕ} {p : Fin 3 → Fin n → ℝ}
    (hp : ∀ i, IsProbability (p i)) :
    iIndepFun finiteRealCoordinate (finiteProductLaw p) := by
  let : ∀ i, IsProbabilityMeasure (finiteWeightLaw (p i)) :=
    fun i => finiteWeightLaw_probability (hp i)
  let := finiteProductLaw_probability hp
  have hEval : iIndepFun (fun i (r : Fin 3 → Fin n) => r i) (finiteProductLaw p) := by
    apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).2
    change (finiteProductLaw p).map id = Measure.pi
      (fun i => (finiteProductLaw p).map (Function.eval i))
    rw [Measure.map_id]
    simp only [finiteProductLaw, (measurePreserving_eval (fun i => finiteWeightLaw (p i)) _).map_eq]
  exact hEval.comp (fun _ (z : Fin n) => (z.val : ℝ)) (fun _ => measurable_of_finite _)

private theorem finiteProductLaw_realRankProfile {n : ℕ} {p : Fin 3 → Fin n → ℝ}
    (hp : ∀ i, IsProbability (p i)) :
    realRankProfile (finiteProductLaw p) finiteRealCoordinate = profile (p 0) (p 1) (p 2) := by
  classical
  let : ∀ i, IsProbabilityMeasure (finiteWeightLaw (p i)) :=
    fun i => finiteWeightLaw_probability (hp i)
  let := finiteProductLaw_probability hp
  funext t
  let A := Finset.univ.filter (fun r : Fin 3 → Fin n =>
    r (rankOrder t 1) < r (rankOrder t 0) ∧ r (rankOrder t 2) < r (rankOrder t 1))
  have hA : rankEvent finiteRealCoordinate t = (A : Set (Fin 3 → Fin n)) := by
    ext r
    simp only [rankEvent, finiteRealCoordinate, Set.mem_ofPred_eq, Finset.mem_coe,
      A, Finset.mem_filter, Finset.mem_univ, true_and, Nat.cast_lt, Fin.val_fin_lt]
  have hmass (r : Fin 3 → Fin n) : (finiteProductLaw p).real {r} = ∏ i, p i (r i) := by
    simp [finiteProductLaw, measureReal_def, Measure.pi_singleton, finiteWeightLaw_singleton,
      ENNReal.toReal_prod, ENNReal.toReal_ofReal ((hp _).1 _)]
  rw [profile_eq_rankMass p, ← sum_rankTuples]
  change (finiteProductLaw p).real (rankEvent finiteRealCoordinate t) = _
  rw [hA, ← sum_measureReal_singleton]
  simp only [hmass, A, Finset.sum_filter]

end FiniteLaw

/-- An arbitrary real realization of a simplex profile passes the finite test. -/
private theorem realRankProfile_mem_finiteTest15 {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin 3 → Ω → ℝ}
    (hX : ∀ i, Measurable (X i)) (hInd : iIndepFun X μ)
    (hs : ∑ t, realRankProfile μ X t = 1) :
    realRankProfile μ X ∈ finiteTest15 := by
  refine isClosed_finiteTest15.mem_of_tendsto (tendsto_quantizedProfile hX hInd hs)
    (Eventually.of_forall fun m => ?_)
  have hd := quantizedWeights_disjoint (μ := μ) hX m
  exact profile_mem_finiteTest15 _ _ _ (quantizedWeights_probability hX m 0)
    (quantizedWeights_probability hX m 1) (quantizedWeights_probability hX m 2)
    (hd (by decide : (0 : Fin 3) ≠ 1)) (hd (by decide : (0 : Fin 3) ≠ 2))
    (hd (by decide : (1 : Fin 3) ≠ 2))

/-- Every profile passing the finite test has an independent finite realization. -/
private theorem finiteTest15_realizable {v : Fin 6 → ℝ} (hv : v ∈ finiteTest15) :
    ∃ μ : Measure (Fin 3 → Fin 15), IsProbabilityMeasure μ ∧
      (∀ i, Measurable (finiteRealCoordinate (n := 15) i)) ∧ iIndepFun finiteRealCoordinate μ ∧
      realRankProfile μ finiteRealCoordinate = v := by
  obtain ⟨a, b, c, ha, hb, hc, _, _, _, h⟩ := hv
  let p : Fin 3 → Fin 15 → ℝ := ![a, b, c]
  have hp (i : Fin 3) : IsProbability (p i) := by
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
  exact ⟨finiteProductLaw p, finiteProductLaw_probability hp,
    finiteRealCoordinate_measurable, finiteRealCoordinate_iIndepFun hp,
    (finiteProductLaw_realRankProfile hp).trans h⟩

end ProbabilityBridge

open MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- For every simplex profile, any independent measurable real realization passes the
fifteen-label cubic test, and any passing profile has an independent real realization
on the finite sample space of label triples. -/
theorem problem_five (v : Fin 6 → ℝ) (hv : (∀ t, 0 ≤ v t) ∧ ∑ t, v t = 1) :
    (∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (X : Fin 3 → Ω → ℝ), (∀ i, Measurable (X i)) → iIndepFun X μ →
      realRankProfile μ X = v → v ∈ finiteTest15) ∧
    (v ∈ finiteTest15 →
      ∃ (μ : Measure (Fin 3 → Fin 15)) (X : Fin 3 → (Fin 3 → Fin 15) → ℝ),
        IsProbabilityMeasure μ ∧ (∀ i, Measurable (X i)) ∧ iIndepFun X μ ∧
          realRankProfile μ X = v) := by
  constructor
  · intro Ω _ μ _ X hX hInd hprofile
    rw [← hprofile]
    exact realRankProfile_mem_finiteTest15 hX hInd (by simpa only [hprofile] using hv.2)
  · intro h
    obtain ⟨μ, hμ, hX, hInd, hprofile⟩ := finiteTest15_realizable h
    exact ⟨μ, finiteRealCoordinate, hμ, hX, hInd, hprofile⟩

end D5.S3.Combinatorics.Dice.RankingProfileRealization
