/- GID: D5/S3/Combinatorics/Dice/RankingProfileRealization
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Dice/RankingProfileRealization
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Caratheodory]
   utility: none
   digest: An exact finite cubic criterion for six strict-order probabilities. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Basic.Real.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Finset.Sort
import Mathlib.Topology.Instances.Real.Lemmas

/-! An exact finite criterion for the full ranking profile in Bozóki, Csató and
Temesi, *Condorcet’s nontransitive dice*, arXiv:2611.23308v1, §5, Problem 5. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Dice.RankingProfileRealization

section FiniteCompression

open Finset
open scoped BigOperators

variable {α : Type*} [Fintype α]

/-- The finite support of the weight function. -/
private noncomputable def weightSupport (p : α → ℝ) : Finset α := by
  classical
  exact univ.filter (fun i => p i ≠ 0)

@[simp] private theorem mem_weightSupport {p : α → ℝ} {i : α} :
    i ∈ weightSupport p ↔ p i ≠ 0 := by
  classical
  simp [weightSupport]

private def IsProbability (p : α → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

/-- Compress a finite convex combination of real vectors using its original input indices. -/
private theorem compressConvexCombination {n : ℕ} (v : α → Fin n → ℝ)
    (p : α → ℝ) (hp : IsProbability p) :
    ∃ q : α → ℝ, IsProbability q ∧ weightSupport q ⊆ weightSupport p ∧
      (weightSupport q).card ≤ n + 1 ∧ ∑ i, q i • v i = ∑ i, p i • v i := by
  classical
  let s := weightSupport p
  have hsum (g : α → ℝ) (hg : ∀ i ∉ s, g i = 0) :
      ∑ i : s, g i = ∑ i, g i := by
    rw [Finset.univ_eq_attach, Finset.sum_attach]
    exact Finset.sum_subset (subset_univ s) (fun i _ hi => hg i hi)
  have hsumVec :
      ∑ i : s, p i • v i = ∑ i, p i • v i := by
    rw [Finset.univ_eq_attach, Finset.sum_attach (f := fun i => p i • v i)]
    apply Finset.sum_subset (subset_univ s)
    intro i _ hi
    have hz : p i = 0 := by simpa [s] using hi
    simp [hz]
  have hull : (∑ i, p i • v i) ∈ convexHull ℝ (Set.range fun i : s => v i) :=
    mem_convexHull_of_exists_fintype (fun i : s => p i) (fun i : s => v i)
      (fun i => hp.1 i) ((hsum p (by intro i hi; simpa [s] using hi)).trans hp.2)
      (fun i => ⟨i, rfl⟩) hsumVec
  obtain ⟨ι, inst, z, w, hz, hind, hwpos, hwone, hwvec⟩ :=
    eq_pos_convex_span_of_mem_convexHull hull
  let _ : Fintype ι := inst
  have preimage (j : ι) : ∃ i : s, v i = z j := hz ⟨j, rfl⟩
  choose pick hpick using preimage
  let f : ι → α := fun j => pick j
  let q : α → ℝ := fun i => ∑ j, if f j = i then w j else 0
  have hmass : (∑ i, q i) = 1 := by
    unfold q
    rw [Finset.sum_comm]
    simpa using hwone
  have hsupport : weightSupport q ⊆ univ.image f := by
    intro i hi
    by_contra h
    have hn (j : ι) : f j ≠ i := fun hji => h (mem_image.mpr ⟨j, mem_univ _, hji⟩)
    exact mem_weightSupport.mp hi (by simp [q, hn])
  refine ⟨q, ⟨fun i => Finset.sum_nonneg fun j _ => ?_, hmass⟩,
    hsupport.trans ?_, ?_, ?_⟩
  · split_ifs
    · exact (hwpos j).le
    · exact le_rfl
  · intro i hi
    obtain ⟨j, -, rfl⟩ := mem_image.mp hi
    exact (pick j).property
  · have hd : Module.finrank ℝ (vectorSpan ℝ (Set.range z)) ≤ n := by
      simpa only [Module.finrank_pi, Fintype.card_fin] using
        (Submodule.finrank_le (vectorSpan ℝ (Set.range z)))
    exact (Finset.card_le_card hsupport).trans
      (Finset.card_image_le.trans (by
        rw [Finset.card_univ]
        exact hind.card_le_finrank_succ.trans (Nat.add_le_add_right hd 1)))
  · unfold q
    simp only [Finset.sum_smul, ite_smul, zero_smul]
    rw [Finset.sum_comm]
    simpa [show ∀ j, v (f j) = z j from hpick] using hwvec

section Ranked

variable [LinearOrder α]

/-- The probability of a strictly decreasing draw from three independent weights. -/
private def rankMass (a b c : α → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, if z < y ∧ y < x then a x * b y * c z else 0

/-- The six coordinates of Eq. (7), in the order XYZ, XZY, YXZ, YZX, ZXY, ZYX. -/
private def profile (a b c : α → ℝ) : Fin 6 → ℝ :=
  ![rankMass a b c, rankMass a c b, rankMass b a c,
    rankMass b c a, rankMass c a b, rankMass c b a]

private def topMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if z < y ∧ y < x then b y * c z else 0

private def middleMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if z < x ∧ x < y then b y * c z else 0

private def bottomMass (b c : α → ℝ) (x : α) : ℝ :=
  ∑ y, ∑ z, if x < z ∧ z < y then b y * c z else 0

private def pairMass (b c : α → ℝ) : ℝ :=
  ∑ y, ∑ z, if z < y then b y * c z else 0

private theorem rank_first (a b c : α → ℝ) :
    rankMass a b c = ∑ x, a x * topMass b c x := by
  unfold rankMass topMass
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_assoc]

private theorem rank_middle (a b c : α → ℝ) :
    rankMass b a c = ∑ x, a x * middleMass b c x := by
  unfold rankMass middleMass
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_left_comm, mul_assoc]

private theorem rank_last (a b c : α → ℝ) :
    rankMass b c a = ∑ x, a x * bottomMass b c x := by
  unfold rankMass bottomMass
  simp_rw [Finset.sum_comm (f := fun z x => if x < z ∧ z < _ then _ else _)]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ =>
    Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp [mul_comm]

private theorem kernel_block (b c : α → ℝ) (x : α) (hx : b x = 0) (hc : c x = 0) :
    topMass b c x + middleMass b c x + bottomMass b c x = pairMass b c := by
  unfold topMass middleMass bottomMass pairMass
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => ?_
  by_cases hyz : z < y
  · rcases lt_trichotomy x z with h | rfl | h
    · have hxy := h.trans hyz
      simp [hyz, h, not_lt_of_gt h, not_lt_of_gt hxy]
    · simp [hc]
    · rcases lt_trichotomy x y with hxy | rfl | hyx
      · simp [hyz, h, hxy, not_lt_of_gt h, not_lt_of_gt hxy]
      · simp [hx]
      · simp [hyz, hyx, not_lt_of_gt h, not_lt_of_gt hyx]
  · have hmid : ¬ (z < x ∧ x < y) := fun h => hyz (h.1.trans h.2)
    simp [hyz, hmid]

private theorem rank_block (a b c : α → ℝ) (ha : IsProbability a)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c)) :
    rankMass a b c + rankMass b a c + rankMass b c a = pairMass b c := by
  rw [rank_first a b c, rank_middle a b c, rank_last a b c]
  simp only [← Finset.sum_add_distrib, ← mul_add]
  calc
    _ = ∑ x, a x * pairMass b c := by
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : a x = 0
      · simp [hx]
      · have hxs := mem_weightSupport.mpr hx
        have hb : b x = 0 := by simpa using (Finset.disjoint_left.mp hab hxs)
        have hc : c x = 0 := by simpa using (Finset.disjoint_left.mp hac hxs)
        rw [kernel_block b c x hb hc]
    _ = _ := by rw [← Finset.sum_mul, ha.2, one_mul]

private def features (b c : α → ℝ) (x : α) : Fin 4 → ℝ :=
  ![topMass b c x, middleMass b c x, topMass c b x, middleMass c b x]

/-- Compress the first weight to five faces while preserving the six rankings. -/
private theorem compressFirst (a b c : α → ℝ) (ha : IsProbability a)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c)) :
    ∃ a' : α → ℝ, IsProbability a' ∧ weightSupport a' ⊆ weightSupport a ∧
      (weightSupport a').card ≤ 5 ∧ profile a' b c = profile a b c := by
  obtain ⟨a', ha', hsub, hcard, hvec⟩ := compressConvexCombination (features b c) a ha
  have hcoord (i : Fin 4) : ∑ x, a' x * features b c x i =
      ∑ x, a x * features b c x i := by
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hvec i
  have h0 : rankMass a' b c = rankMass a b c := by
    rw [rank_first a' b c, rank_first a b c]
    simpa [features] using hcoord 0
  have h1 : rankMass b a' c = rankMass b a c := by
    rw [rank_middle a' b c, rank_middle a b c]
    simpa [features] using hcoord 1
  have h2 : rankMass a' c b = rankMass a c b := by
    rw [rank_first a' c b, rank_first a c b]
    simpa [features] using hcoord 2
  have h3 : rankMass c a' b = rankMass c a b := by
    rw [rank_middle a' c b, rank_middle a c b]
    simpa [features] using hcoord 3
  have hab' := hab.mono_left hsub
  have hac' := hac.mono_left hsub
  have h4 : rankMass b c a' = rankMass b c a := by
    have h := rank_block a' b c ha' hab' hac'
    rw [h0, h1] at h
    exact add_left_cancel (h.trans (rank_block a b c ha hab hac).symm)
  have h5 : rankMass c b a' = rankMass c b a := by
    have h := rank_block a' c b ha' hac' hab'
    rw [h2, h3] at h
    exact add_left_cancel (h.trans (rank_block a c b ha hac hab).symm)
  exact ⟨a', ha', hsub, hcard, by simp only [profile, h0, h1, h2, h3, h4, h5]⟩

private theorem rotate_profile {a b c a' b' c' : α → ℝ}
    (h : profile a b c = profile a' b' c') :
    profile c a b = profile c' a' b' := by
  funext i
  fin_cases i
  · exact congrFun h 4
  · exact congrFun h 5
  · exact congrFun h 1
  · exact congrFun h 0
  · exact congrFun h 3
  · exact congrFun h 2

/-- Compress all three probability weights on their original ordered type. -/
private theorem compressFinite (a b c : α → ℝ)
    (ha : IsProbability a) (hb : IsProbability b) (hc : IsProbability c)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c))
    (hbc : Disjoint (weightSupport b) (weightSupport c)) :
    ∃ a' b' c' : α → ℝ,
      IsProbability a' ∧ IsProbability b' ∧ IsProbability c' ∧
      weightSupport a' ⊆ weightSupport a ∧ weightSupport b' ⊆ weightSupport b ∧
      weightSupport c' ⊆ weightSupport c ∧
      (weightSupport a').card ≤ 5 ∧ (weightSupport b').card ≤ 5 ∧
      (weightSupport c').card ≤ 5 ∧ profile a' b' c' = profile a b c := by
  obtain ⟨a', ha', hsa, hca, hpa⟩ := compressFirst a b c ha hab hac
  obtain ⟨b', hb', hsb, hcb, hpb⟩ :=
    compressFirst b c a' hb hbc (hab.mono_left hsa).symm
  obtain ⟨c', hc', hsc, hcc, hpc⟩ :=
    compressFirst c a' b' hc (hac.mono_left hsa).symm (hbc.mono_left hsb).symm
  exact ⟨a', b', c', ha', hb', hc', hsa, hsb, hsc, hca, hcb, hcc,
    (rotate_profile (rotate_profile hpc)).trans ((rotate_profile hpb).trans hpa)⟩

end Ranked

end FiniteCompression

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

private theorem iIndepFun_Q (hX : ProbabilityTheory.iIndepFun X μ) (m : ℕ) :
    ProbabilityTheory.iIndepFun (fun i ω => Q m i (X i ω)) μ :=
  hX.comp (Q m) (measurable_Q m)

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

section FiniteGrid

open scoped BigOperators

/-- The attainable profiles on `n` labels with at most `cap` positive weights per die. -/
private def finiteTest (n cap : ℕ) : Set (Fin 6 → ℝ) :=
  {v | ∃ a b c : Fin n → ℝ,
    IsProbability a ∧ IsProbability b ∧ IsProbability c ∧
    ((Finset.univ.filter fun i => 0 < a i).card ≤ cap) ∧
    ((Finset.univ.filter fun i => 0 < b i).card ≤ cap) ∧
    ((Finset.univ.filter fun i => 0 < c i).card ≤ cap) ∧
    profile a b c = v}

/-- The finite test with fifteen common ordered labels and five faces per die. -/
def finiteTest15 : Set (Fin 6 → ℝ) := finiteTest 15 5

private theorem positiveSupport_eq {α : Type*} [Fintype α] {p : α → ℝ}
    (hp : IsProbability p) : (Finset.univ.filter fun i => 0 < p i) = weightSupport p := by
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_weightSupport]
  exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hp.1 i) (Ne.symm h)⟩

private def simplexFace {n : ℕ} (s : Finset (Fin n)) : Set (Fin n → ℝ) :=
  {p | IsProbability p ∧ ∀ i ∉ s, p i = 0}

private theorem isCompact_simplexFace {n : ℕ} (s : Finset (Fin n)) :
    IsCompact (simplexFace s) := by
  classical
  have hFace : simplexFace s =
      ((⋂ i : Fin n, {p : Fin n → ℝ | 0 ≤ p i}) ∩
        {p : Fin n → ℝ | ∑ i, p i = 1}) ∩
      (⋂ i : {i : Fin n // i ∉ s}, {p : Fin n → ℝ | p i = 0}) := by
    ext p
    simp [simplexFace, IsProbability]
  have hClosed : IsClosed (simplexFace s) := by
    rw [hFace]
    refine (IsClosed.inter (isClosed_iInter fun i => ?_) ?_).inter
      (isClosed_iInter fun i => ?_)
    · exact isClosed_le continuous_const (continuous_apply i)
    · exact isClosed_eq (continuous_finsetSum _ fun i _ => continuous_apply i)
        continuous_const
    · exact isClosed_eq (continuous_apply i.val) continuous_const
  have hBox : IsCompact (Set.Icc (0 : Fin n → ℝ) 1) := isCompact_Icc
  refine hBox.of_isClosed_subset hClosed ?_
  intro p hp
  change IsProbability p ∧ (∀ i ∉ s, p i = 0) at hp
  refine ⟨hp.1.1, fun i => ?_⟩
  change p i ≤ (1 : ℝ)
  rw [← hp.1.2]
  exact Finset.single_le_sum (f := p) (fun j _ => hp.1.1 j) (Finset.mem_univ i)

private def cappedSimplex (n cap : ℕ) : Set (Fin n → ℝ) :=
  ⋃ s : {s : Finset (Fin n) // s.card ≤ cap}, simplexFace s.val

private theorem mem_cappedSimplex {n cap : ℕ} {p : Fin n → ℝ} :
    p ∈ cappedSimplex n cap ↔
      IsProbability p ∧ (Finset.univ.filter fun i => 0 < p i).card ≤ cap := by
  simp only [cappedSimplex, Set.mem_iUnion]
  constructor
  · rintro ⟨⟨s, hs⟩, hp, hz⟩
    refine ⟨hp, ?_⟩
    rw [positiveSupport_eq hp]
    refine (Finset.card_le_card (show weightSupport p ⊆ s from ?_)).trans hs
    intro i hi
    exact Classical.byContradiction fun h => mem_weightSupport.mp hi (hz i h)
  · rintro ⟨hp, hCard⟩
    rw [positiveSupport_eq hp] at hCard
    exact ⟨⟨weightSupport p, hCard⟩, hp, fun i hi => by simpa using hi⟩

private theorem continuous_profile {n : ℕ} :
    Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      profile p.1 p.2.1 p.2.2) := by
  have rank {X : Type} [TopologicalSpace X] {a b c : X → Fin n → ℝ}
      (ha : Continuous a) (hb : Continuous b) (hc : Continuous c) :
      Continuous (fun p => rankMass (a p) (b p) (c p)) := by
    unfold rankMass
    refine continuous_finsetSum _ fun i _ =>
      continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => ?_
    by_cases h : k < j ∧ j < i
    · simp only [ite_eq_left h]
      have hai : Continuous (fun p => a p i) := (continuous_apply i).comp ha
      have hbj : Continuous (fun p => b p j) := (continuous_apply j).comp hb
      have hck : Continuous (fun p => c p k) := (continuous_apply k).comp hc
      exact (hai.mul hbj).mul hck
    · simp only [ite_eq_right h]
      exact continuous_const
  have ha : Continuous (Prod.fst : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) → _) :=
    continuous_fst
  have hb : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.1) :=
    continuous_fst.comp continuous_snd
  have hc : Continuous (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) => p.2.2) :=
    continuous_snd.comp continuous_snd
  apply continuous_pi
  intro i
  fin_cases i
  · exact rank ha hb hc
  · exact rank ha hc hb
  · exact rank hb ha hc
  · exact rank hb hc ha
  · exact rank hc ha hb
  · exact rank hc hb ha

/-- The profile image of the finite union of products of simplex faces is compact. -/
private theorem isCompact_finiteTest (n cap : ℕ) : IsCompact (finiteTest n cap) := by
  have h : IsCompact (cappedSimplex n cap) :=
    isCompact_iUnion fun s => isCompact_simplexFace s.val
  have hImage : (fun p : (Fin n → ℝ) × (Fin n → ℝ) × (Fin n → ℝ) =>
      profile p.1 p.2.1 p.2.2) '' ((cappedSimplex n cap).prod
        ((cappedSimplex n cap).prod (cappedSimplex n cap))) = finiteTest n cap := by
    ext v
    constructor
    · rintro ⟨⟨a, b, c⟩, ⟨ha, hb, hc⟩, hv⟩
      obtain ⟨ha, hca⟩ := mem_cappedSimplex.mp ha
      obtain ⟨hb, hcb⟩ := mem_cappedSimplex.mp hb
      obtain ⟨hc, hcc⟩ := mem_cappedSimplex.mp hc
      exact ⟨a, b, c, ha, hb, hc, hca, hcb, hcc, hv⟩
    · rintro ⟨a, b, c, ha, hb, hc, hca, hcb, hcc, hv⟩
      exact ⟨(a, b, c), ⟨mem_cappedSimplex.mpr ⟨ha, hca⟩,
        mem_cappedSimplex.mpr ⟨hb, hcb⟩, mem_cappedSimplex.mpr ⟨hc, hcc⟩⟩, hv⟩
  rw [← hImage]
  exact (h.prod (h.prod h)).image continuous_profile

private theorem isClosed_finiteTest (n cap : ℕ) : IsClosed (finiteTest n cap) :=
  (isCompact_finiteTest n cap).isClosed

private theorem isClosed_finiteTest15 : IsClosed finiteTest15 :=
  isClosed_finiteTest 15 5

section Relabel

variable {ι α : Type*} [Fintype ι] [Fintype α]

private theorem sum_reindex (e : ι ↪ α) (f : α → ℝ)
    (hz : ∀ x ∉ Set.range e, f x = 0) :
    (∑ i, f (e i)) = ∑ x, f x := by
  rw [← Finset.sum_map]
  refine Finset.sum_subset (Finset.subset_univ _) fun x _ hx => hz x ?_
  rintro ⟨i, rfl⟩
  exact hx (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

private theorem probability_comp (e : ι ↪ α) {p : α → ℝ} (hp : IsProbability p)
    (hz : ∀ x ∉ Set.range e, p x = 0) : IsProbability (fun i => p (e i)) :=
  ⟨fun i => hp.1 (e i), (sum_reindex e p hz).trans hp.2⟩

private theorem card_weightSupport_comp (e : ι ↪ α) (p : α → ℝ)
    (hz : ∀ x ∉ Set.range e, p x = 0) :
    (weightSupport (fun i => p (e i))).card = (weightSupport p).card := by
  have hMap : (weightSupport (fun i => p (e i))).map e = weightSupport p := by
    ext x
    simp only [Finset.mem_map, mem_weightSupport]
    constructor
    · rintro ⟨_, hi, rfl⟩
      exact hi
    · intro hx
      have hr : x ∈ Set.range e := Classical.byContradiction fun h => hx (hz x h)
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, hx, rfl⟩
  rw [← hMap, Finset.card_map]

variable [LinearOrder ι] [LinearOrder α]

private theorem rankMass_comp (e : ι ↪o α) (a b c : α → ℝ)
    (ha : ∀ x ∉ Set.range e, a x = 0) (hb : ∀ x ∉ Set.range e, b x = 0)
    (hc : ∀ x ∉ Set.range e, c x = 0) :
    rankMass (fun i => a (e i)) (fun i => b (e i)) (fun i => c (e i)) =
      rankMass a b c := by
  let term (x y z : α) := if z < y ∧ y < x then a x * b y * c z else 0
  calc
    _ = ∑ i, ∑ j, ∑ k, term (e i) (e j) (e k) := by
      simp only [rankMass, term, e.lt_iff_lt]
    _ = ∑ x, ∑ y, ∑ z, term x y z := by
      calc
        _ = ∑ i, ∑ j, ∑ z, term (e i) (e j) z := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
            sum_reindex e.toEmbedding (term (e i) (e j)) ?_
          intro z hz
          simp [term, hc z hz]
        _ = ∑ i, ∑ y, ∑ z, term (e i) y z := by
          refine Finset.sum_congr rfl fun i _ =>
            sum_reindex e.toEmbedding (fun y => ∑ z, term (e i) y z) ?_
          intro y hy
          simp [term, hb y hy]
        _ = _ := by
          refine sum_reindex e.toEmbedding (fun x => ∑ y, ∑ z, term x y z) ?_
          intro x hx
          simp [term, ha x hx]
    _ = _ := rfl

/-- Restricting to an increasing enumeration that contains all three supports preserves the
existing six coordinates in their original order. -/
private theorem profile_comp_orderEmbedding (e : ι ↪o α) (a b c : α → ℝ)
    (ha : ∀ x ∉ Set.range e, a x = 0) (hb : ∀ x ∉ Set.range e, b x = 0)
    (hc : ∀ x ∉ Set.range e, c x = 0) :
    profile (fun i => a (e i)) (fun i => b (e i)) (fun i => c (e i)) =
      profile a b c := by
  simp only [profile, rankMass_comp e a b c ha hb hc, rankMass_comp e a c b ha hc hb,
    rankMass_comp e b a c hb ha hc, rankMass_comp e b c a hb hc ha,
    rankMass_comp e c a b hc ha hb, rankMass_comp e c b a hc hb ha]

end Relabel

/-- Sort a finite set containing the three supports and pad the remaining labels with zeros. -/
private theorem profile_mem_finiteTest_of_support_subset {α : Type*} [Fintype α] [LinearOrder α]
    {n cap : ℕ} (a b c : α → ℝ) (ha : IsProbability a) (hb : IsProbability b)
    (hc : IsProbability c) (s : Finset α) (hs : s.card ≤ n)
    (hsa : weightSupport a ⊆ s) (hsb : weightSupport b ⊆ s) (hsc : weightSupport c ⊆ s)
    (hca : (weightSupport a).card ≤ cap) (hcb : (weightSupport b).card ≤ cap)
    (hcc : (weightSupport c).card ≤ cap) :
    profile a b c ∈ finiteTest n cap := by
  let e := s.orderEmbOfFin rfl
  let d := Fin.castLEOrderEmb hs
  let pad (p : α → ℝ) : Fin n → ℝ := Function.extend d (fun i => p (e i)) (fun _ => 0)
  have hzero {p : α → ℝ} (hp : weightSupport p ⊆ s) :
      ∀ x ∉ Set.range e, p x = 0 := by
    intro x hx
    by_contra h
    exact hx ((s.range_orderEmbOfFin rfl).symm ▸ show x ∈ (s : Set α) from
      hp (mem_weightSupport.mpr h))
  have hPad (p : α → ℝ) (i : Fin s.card) : pad p (d i) = p (e i) :=
    d.injective.extend_apply _ _ i
  have hPadZero (p : α → ℝ) : ∀ x ∉ Set.range d, pad p x = 0 := by
    intro x hx
    exact Function.extend_apply' _ _ _ hx
  have hPadProb (p : α → ℝ) (hp : IsProbability p) (hsp : weightSupport p ⊆ s) :
      IsProbability (pad p) := by
    refine ⟨fun x => ?_, ?_⟩
    · by_cases hx : x ∈ Set.range d
      · obtain ⟨i, rfl⟩ := hx
        rw [hPad]
        exact hp.1 _
      · rw [hPadZero p x hx]
    · rw [← sum_reindex d.toEmbedding (pad p) (hPadZero p)]
      change (∑ i, pad p (d i)) = 1
      simp only [hPad]
      exact (probability_comp e.toEmbedding hp (hzero hsp)).2
  have hCard (p : α → ℝ) (hp : IsProbability (pad p)) (hsp : weightSupport p ⊆ s) :
      (Finset.univ.filter fun i => 0 < pad p i).card = (weightSupport p).card := by
    rw [positiveSupport_eq hp, ← card_weightSupport_comp d.toEmbedding (pad p) (hPadZero p)]
    change (weightSupport (fun i => pad p (d i))).card = (weightSupport p).card
    simp only [hPad]
    exact card_weightSupport_comp e.toEmbedding p (hzero hsp)
  have hpa := hPadProb a ha hsa
  have hpb := hPadProb b hb hsb
  have hpc := hPadProb c hc hsc
  refine ⟨pad a, pad b, pad c, hpa, hpb, hpc, ?_, ?_, ?_, ?_⟩
  · rw [hCard a hpa hsa]
    exact hca
  · rw [hCard b hpb hsb]
    exact hcb
  · rw [hCard c hpc hsc]
    exact hcc
  · rw [← profile_comp_orderEmbedding d (pad a) (pad b) (pad c)
      (hPadZero a) (hPadZero b) (hPadZero c)]
    simp only [hPad]
    exact profile_comp_orderEmbedding e a b c (hzero hsa) (hzero hsb) (hzero hsc)

/-- Three finite probability weights on a common linear order with pairwise disjoint supports
give a profile in the fifteen-label finite test. -/
private theorem profile_mem_finiteTest15 {α : Type*} [Fintype α] [LinearOrder α]
    (a b c : α → ℝ) (ha : IsProbability a) (hb : IsProbability b) (hc : IsProbability c)
    (hab : Disjoint (weightSupport a) (weightSupport b))
    (hac : Disjoint (weightSupport a) (weightSupport c))
    (hbc : Disjoint (weightSupport b) (weightSupport c)) :
    profile a b c ∈ finiteTest15 := by
  obtain ⟨a', b', c', ha', hb', hc', -, -, -, hca, hcb, hcc, hp⟩ :=
    compressFinite a b c ha hb hc hab hac hbc
  let s := weightSupport a' ∪ weightSupport b' ∪ weightSupport c'
  have hs : s.card ≤ 15 := by
    have hab' := Finset.card_union_le (weightSupport a') (weightSupport b')
    have habc' := Finset.card_union_le (weightSupport a' ∪ weightSupport b') (weightSupport c')
    change (weightSupport a' ∪ weightSupport b' ∪ weightSupport c').card ≤ 15
    omega
  rw [← hp]
  apply profile_mem_finiteTest_of_support_subset a' b' c' ha' hb' hc' s hs
      _ _ _ hca hcb hcc
  · exact Finset.subset_union_left.trans Finset.subset_union_left
  · exact Finset.subset_union_right.trans Finset.subset_union_left
  · exact Finset.subset_union_right

end FiniteGrid

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
  · exact (mem_weightSupport.1 hi) hz
  · exact (mem_weightSupport.1 hj) hz

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
