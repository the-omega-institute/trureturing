/- GID: D5/S3/Observer/Budget/SparseGridIntegrability
   generality: G
   mirror-B: D5/B/S3/Observer/Budget/SparseGridIntegrability
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: All-law integrability of actual sparse-grid rounding and a common first-zero witness. -/

import D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.MeasurableSpace.Embedding
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic

noncomputable section
open MeasureTheory Filter Finset
open scoped ENNReal Topology BigOperators

namespace D5.S3.Observer.Budget.SparseGridIntegrability

/-- Arbitrary retained depths, without a computability hypothesis. -/
structure Grid where
  depth : ℕ → ℕ
  zero : depth 0 = 0
  increasing : StrictMono depth

private lemma grid_cofinal (S : Grid) (n : ℕ) : ∃ j, n ≤ S.depth j :=
  ⟨n, S.increasing.id_le n⟩

/-- The actual least retained depth at least `n`, including `round S 0 = 0`. -/
def round (S : Grid) (n : ℕ) : ℕ := S.depth (Nat.find (grid_cofinal S n))

private lemma le_round (S : Grid) (n : ℕ) : n ≤ round S n :=
  Nat.find_spec (grid_cofinal S n)

private lemma round_le (S : Grid) {n j : ℕ} (h : n ≤ S.depth j) :
    round S n ≤ S.depth j :=
  S.increasing.monotone (Nat.find_min' (grid_cofinal S n) h)

private lemma round_depth (S : Grid) (j : ℕ) : round S (S.depth j) = S.depth j :=
  le_antisymm (round_le S le_rfl) (le_round S _)

private lemma round_zero (S : Grid) : round S 0 = 0 := by
  simpa only [S.zero] using round_depth S 0

private lemma round_segment (S : Grid) {n j : ℕ}
    (lo : S.depth j < n) (hi : n ≤ S.depth (j + 1)) :
    round S n = S.depth (j + 1) := by
  apply le_antisymm (round_le S hi)
  unfold round
  apply S.increasing.monotone
  have hf := Nat.find_spec (grid_cofinal S n)
  by_contra h
  have : Nat.find (grid_cofinal S n) ≤ j := by omega
  have := S.increasing.monotone this
  omega

/-- Global extended rounding ratio, with positive integer denominator. -/
def ratio (S : Grid) : ℝ≥0∞ :=
  ⨆ n : ℕ, (round S (n + 1) : ℝ≥0∞) / (n + 1 : ℕ)

/-- The equivalent supremum taken at the first positive depth of each segment. -/
def segmentRatio (S : Grid) : ℝ≥0∞ :=
  ⨆ j : ℕ, (S.depth (j + 1) : ℝ≥0∞) / (S.depth j + 1 : ℕ)

/-- One common finite linear bound on all positive depths. -/
def LinearBound (S : Grid) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (round S n : ℝ) ≤ C * n

private lemma ratio_eq_segmentRatio (S : Grid) : ratio S = segmentRatio S := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    let j := Nat.find (grid_cofinal S (n + 1))
    have hj : 0 < j := by
      have hf : n + 1 ≤ S.depth j := Nat.find_spec (grid_cofinal S (n + 1))
      by_contra h
      have hz : j = 0 := by omega
      rw [hz, S.zero] at hf
      omega
    have hlo : S.depth (j - 1) < n + 1 := by
      exact Nat.lt_of_not_ge (Nat.find_min (grid_cofinal S (n + 1)) (by omega))
    have hden : (S.depth (j - 1) + 1 : ℕ) ≤ n + 1 := by omega
    calc
      (round S (n + 1) : ℝ≥0∞) / (n + 1 : ℕ) ≤
          (S.depth j : ℝ≥0∞) / (S.depth (j - 1) + 1 : ℕ) := by
        change (S.depth j : ℝ≥0∞) / (n + 1 : ℕ) ≤ _
        gcongr
      _ ≤ segmentRatio S := by
        have h := le_iSup (fun i : ℕ =>
          (S.depth (i + 1) : ℝ≥0∞) / (S.depth i + 1 : ℕ)) (j - 1)
        simpa only [Nat.sub_add_cancel hj, segmentRatio] using h
  · refine iSup_le fun j => ?_
    have hr := round_segment S (Nat.lt_succ_self (S.depth j))
      (S.increasing (Nat.lt_succ_self j))
    exact hr ▸ le_iSup (fun n : ℕ =>
      (round S (n + 1) : ℝ≥0∞) / (n + 1 : ℕ)) (S.depth j)

/-- The exact source weights, indexed by `k+1` to exclude zero. -/
def weight (t : ℕ → ℕ) (k : ℕ) : ℝ :=
  1 / (4 * (k + 1 : ℝ) ^ 2 * t k)

/-- The countably atomic separating law, with the remaining mass at depth one. -/
def atomicLaw (t : ℕ → ℕ) : Measure ℕ :=
  ENNReal.ofReal (1 - ∑' k, weight t k) • Measure.dirac 1 +
    Measure.sum (fun k => ENNReal.ofReal (weight t k) • Measure.dirac (t k))

private lemma inverse_square_summable :
    Summable (fun k : ℕ => 1 / (k + 1 : ℝ) ^ 2) := by
  simpa only [Nat.cast_add, Nat.cast_one] using
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))

private lemma inverse_square_sum_le :
    (∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) ≤ 2 := by
  apply Real.tsum_le_of_sum_range_le (fun k => by positivity)
  intro n
  have h := (sum_Ioo_inv_sq_le (α := ℝ) 0 (n + 1))
  have heq : (∑ k ∈ range n, 1 / (k + 1 : ℝ) ^ 2) =
      ∑ k ∈ Ioo 0 (n + 1), ((k : ℝ) ^ 2)⁻¹ := by
    apply Finset.sum_bij (fun k _ => k + 1)
    · intro k hk
      simp only [mem_range] at hk
      simp only [mem_Ioo]
      omega
    · intro a ha b hb hab
      omega
    · intro j hj
      simp only [mem_Ioo] at hj
      exact ⟨j - 1, by simp only [mem_range]; omega, by omega⟩
    · intro k hk
      simp only [Nat.cast_add, Nat.cast_one, one_div]
  simpa only [heq, Nat.cast_zero, zero_add, div_one] using h

private lemma weight_bounds (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    Summable (weight t) ∧ (∑' k, weight t k) ≤ 1 / 4 ∧
      Summable (fun k => weight t k * (Nat.cast (t k) : ℝ)) := by
  have hp (k : ℕ) : 0 ≤ weight t k := by unfold weight; positivity
  have hu (k : ℕ) : weight t k ≤ (1 / 8) * (1 / (k + 1 : ℝ) ^ 2) := by
    have htk : (2 : ℝ) ≤ t k := by exact_mod_cast ht k
    unfold weight
    have hk : 0 < (k + 1 : ℝ) ^ 2 := by positivity
    apply (div_le_iff₀ (by positivity : 0 < 4 * (k + 1 : ℝ) ^ 2 * t k)).2
    field_simp
    nlinarith
  have hs := Summable.of_nonneg_of_le hp hu (inverse_square_summable.mul_left (1 / 8))
  have hmass : (∑' k, weight t k) ≤ 1 / 4 := by
    calc
      (∑' k, weight t k) ≤ ∑' k : ℕ, (1 / 8 : ℝ) * (1 / (k + 1 : ℝ) ^ 2) :=
        hs.tsum_le_tsum hu (inverse_square_summable.mul_left (1 / 8))
      _ = (1 / 8 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2 := tsum_mul_left
      _ ≤ 1 / 4 := by nlinarith [inverse_square_sum_le]
  refine ⟨hs, hmass, ?_⟩
  apply (inverse_square_summable.mul_left (1 / 4 : ℝ)).congr
  intro k
  have htk : (Nat.cast (t k) : ℝ) ≠ 0 := by exact_mod_cast (show t k ≠ 0 by have := ht k; omega)
  unfold weight
  field_simp
  <;> ring

private lemma atomic_probability (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    IsProbabilityMeasure (atomicLaw t) := by
  obtain ⟨hs, hmass, _⟩ := weight_bounds t ht
  have hpos : 0 ≤ 1 - ∑' k, weight t k := by linarith
  constructor
  simp only [atomicLaw, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_univ _), mul_one, Measure.sum_apply _ MeasurableSet.univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by unfold weight; positivity) hs,
    ← ENNReal.ofReal_add hpos (tsum_nonneg (fun k => by unfold weight; positivity))]
  norm_num

private lemma atomic_integrable (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    Integrable (fun n : ℕ => (n : ℝ)) (atomicLaw t) := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  · apply integrable_sum_dirac (fun _ => ENNReal.ofReal_ne_top)
    have hp : ∀ k, 0 ≤ weight t k := fun k => by unfold weight; positivity
    simpa only [ENNReal.toReal_ofReal (hp _), Real.norm_natCast] using
      (weight_bounds t ht).2.2

private lemma linear_iff_bigO (S : Grid) :
    LinearBound S ↔ (fun n : ℕ => (round S n : ℝ)) =O[atTop] (fun n => (n : ℝ)) := by
  constructor
  · rintro ⟨C, _, hC⟩
    exact Asymptotics.IsBigO.of_bound C (Eventually.of_forall (by simpa using hC))
  · intro h
    obtain ⟨C, hC, hb⟩ := Asymptotics.bound_of_isBigO_nat_atTop h
    refine ⟨C, hC.le, fun n => ?_⟩
    by_cases hn : n = 0
    · simp [hn, round_zero]
    · simpa using hb (by exact_mod_cast hn : (n : ℝ) ≠ 0)

private lemma linear_iff_ratio (S : Grid) : LinearBound S ↔ ratio S < ∞ := by
  constructor
  · rintro ⟨C, hC, hb⟩
    apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
    refine iSup_le fun n => ?_
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_div_of_pos (by positivity : 0 < ((n + 1 : ℕ) : ℝ))]
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_iff₀ (by positivity)).2 (hb (n + 1))
  · intro h
    refine ⟨(ratio S).toReal, ENNReal.toReal_nonneg, fun n => ?_⟩
    cases n with
    | zero => simp [round_zero]
    | succ n =>
      have hb := ENNReal.toReal_mono h.ne (le_iSup
        (fun k : ℕ => (round S (k + 1) : ℝ≥0∞) / (k + 1 : ℕ)) n)
      simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hb
      exact (div_le_iff₀ (by positivity : (0 : ℝ) < (n + 1 : ℕ))).1 hb

private lemma bad_tail (S : Grid) (h : ¬LinearBound S) (B : ℝ) (N : ℕ) :
    ∃ n, N < n ∧ B * n ≤ (round S n : ℝ) := by
  by_contra hn
  push_neg at hn
  apply h
  apply (linear_iff_bigO S).2
  apply Asymptotics.IsBigO.of_bound B
  filter_upwards [eventually_gt_atTop N] with n hn'
  simpa only [Real.norm_natCast] using (hn n hn').le

private lemma exists_bad_depths (S : Grid) (h : ¬LinearBound S) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      (∀ k, 2 ≤ t k) ∧
      ∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (Nat.cast (t k) : ℝ) ≤ (round S (t k) : ℝ) := by
  classical
  let step (k n : ℕ) := (bad_tail S h ((k + 1 : ℝ) ^ 3) (max n 1)).choose
  have step_spec (k n : ℕ) :
      max n 1 < step k n ∧
      (k + 1 : ℝ) ^ 3 * step k n ≤ (round S (step k n) : ℝ) :=
    (bad_tail S h ((k + 1 : ℝ) ^ 3) (max n 1)).choose_spec
  let t : ℕ → ℕ := Nat.rec (step 0 1) (fun k prev => step (k + 1) prev)
  have ht (k : ℕ) : 2 ≤ t k ∧
      (k + 1 : ℝ) ^ 3 * (Nat.cast (t k) : ℝ) ≤ (round S (t k) : ℝ) := by
    cases k with
    | zero => exact ⟨by have := (step_spec 0 1).1; dsimp [t]; omega,
        (step_spec 0 1).2⟩
    | succ k => exact ⟨by have := (step_spec (k + 1) (t k)).1; change 2 ≤ step (k+1) (t k); omega,
        (step_spec (k + 1) (t k)).2⟩
  refine ⟨t, strictMono_nat_of_lt_succ (fun k => ?_), fun k => (ht k).1,
    fun k => (ht k).2⟩
  exact lt_of_le_of_lt (le_max_left (t k) 1) (step_spec (k + 1) (t k)).1

private lemma atomic_not_integrable (S : Grid) (t : ℕ → ℕ)
    (ht : ∀ k, 2 ≤ t k)
    (hg : ∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (Nat.cast (t k) : ℝ) ≤ (round S (t k) : ℝ)) :
    ¬Integrable (fun n : ℕ => (round S n : ℝ)) (atomicLaw t) := by
  intro hi
  have hseries := (integrable_add_measure.mp hi).2.summable_of_dirac
  have hp : ∀ k, 0 ≤ weight t k := fun k => by unfold weight; positivity
  simp only [ENNReal.toReal_ofReal (hp _), Real.norm_natCast] at hseries
  have hlow (k : ℕ) : (k + 1 : ℝ) / 4 ≤ weight t k * (round S (t k) : ℝ) := by
    have htk : (0 : ℝ) < t k := by exact_mod_cast (show 0 < t k by have := ht k; omega)
    have hk : (0 : ℝ) < k + 1 := by positivity
    unfold weight
    rw [one_div_mul_eq_div]
    apply (le_div_iff₀ (by positivity : 0 < 4 * (k + 1 : ℝ) ^ 2 * t k)).2
    have heq : (k + 1 : ℝ) / 4 * (4 * (k + 1 : ℝ) ^ 2 * t k) =
        (k + 1 : ℝ) ^ 3 * t k := by ring
    rw [heq]
    exact hg k
  have hconst : Summable (fun _ : ℕ => (1 / 4 : ℝ)) :=
    Summable.of_nonneg_of_le (fun _ => by norm_num)
      (fun k => (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith : (1 / 4 : ℝ) ≤ (k + 1 : ℝ) / 4).trans (hlow k)) hseries
  norm_num [summable_const_iff] at hconst

universe u

/-- Preservation for every measurable positive integer variable on every probability space. -/
def AllLaw (S : Grid) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (T : Ω → ℕ), Measurable T → (∀ x, 1 ≤ T x) →
      Integrable (fun x => (T x : ℝ)) μ →
      Integrable (fun x => (round S (T x) : ℝ)) μ

private lemma linear_preserves (S : Grid) (hb : LinearBound S) : AllLaw.{u} S := by
  rintro Ω mΩ μ hμ T hT _ hi
  obtain ⟨C, hC, hb⟩ := hb
  apply (hi.const_mul C).mono' ((measurable_of_countable
    (fun n : ℕ => (round S n : ℝ))).comp hT).aestronglyMeasurable
  exact Eventually.of_forall (fun x => by simpa only [Function.comp_apply, Real.norm_natCast] using hb (T x))

private lemma atomic_positive (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    ∀ᵐ n ∂atomicLaw t, 1 ≤ n := by
  rw [ae_iff]
  have heq : {n : ℕ | ¬1 ≤ n} = {0} := by ext n; simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]; omega
  rw [heq]
  have hn : ∀ k, t k ≠ 0 := fun k => by have := ht k; omega
  simp [atomicLaw, Measure.sum_apply, hn]

private lemma allLaw_implies_linear (S : Grid) (h : AllLaw.{u} S) : LinearBound S := by
  by_contra hn
  obtain ⟨t, _, ht, hg⟩ := exists_bad_depths S hn
  let μ := atomicLaw t
  letI : IsProbabilityMeasure μ := atomic_probability t ht
  let ν := Measure.map (ULift.up : ℕ → ULift.{u} ℕ) μ
  letI : IsProbabilityMeasure ν := inferInstance
  let T : ULift.{u} ℕ → ℕ := fun x => max x.down 1
  have hT : Measurable T := (measurable_of_countable (fun n : ℕ => max n 1)).comp measurable_down
  have hcongr : (fun n : ℕ => ((max n 1 : ℕ) : ℝ)) =ᵐ[μ] (fun n => (n : ℝ)) := by
    filter_upwards [atomic_positive t ht] with n hn
    rw [max_eq_left hn]
  have hi : Integrable (fun x => (T x : ℝ)) ν := by
    apply (integrable_map_measure
      ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hT).aestronglyMeasurable
      measurable_up.aemeasurable).2
    simpa only [Function.comp_def, T, ULift.down_up] using
      (atomic_integrable t ht).congr hcongr.symm
  have hr := h _ ν T hT (fun x => le_max_right _ _) hi
  have hr' := (integrable_map_measure
    ((measurable_of_countable (fun n : ℕ => (round S n : ℝ))).comp hT).aestronglyMeasurable
    measurable_up.aemeasurable).1 hr
  apply atomic_not_integrable S t ht hg
  apply hr'.congr
  filter_upwards [atomic_positive t ht] with n hn
  simp only [Function.comp_apply, T, ULift.down_up, max_eq_left hn]

/-- First-zero code over any finite alphabet with distinct zero and one. -/
def firstZeroCode {A : Type*} (zero one : A) : Set (List A) :=
  Set.range (fun n : ℕ => List.replicate n one ++ [zero])

/-- The path with first zero exactly at a specified positive depth. -/
def depthPath {A : Type*} (zero one : A) (n : ℕ) : ℕ → A :=
  fun i => if i + 1 < n then one else zero

/-- Rounding extended to genuine infinite no-hit times. -/
def extendedRound (S : Grid) (t : ℝ≥0∞) : ℝ≥0∞ :=
  if t = ∞ then ∞ else (round S ⌊t.toReal⌋₊ : ℝ≥0∞)

/-- One common Borel law on paths, the pushforward of the exact atomic depth law. -/
def prefixLaw {A : Type*} [MeasurableSpace A] (zero one : A) (t : ℕ → ℕ) :
    Measure (ℕ → A) := Measure.map (depthPath zero one) (atomicLaw t)

private lemma measurable_depthPath {A : Type*} [MeasurableSpace A] (zero one : A) :
    Measurable (depthPath zero one) := measurable_of_countable _

private lemma first_zero_prefix_free {A : Type*} (zero one : A) (hne : one ≠ zero) :
    D5.S0.Computability.Coding.PrefixFreeCode.IsPrefixFree (firstZeroCode zero one) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ hp
  have hlen := hp.length_le
  simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
  have hmn : m = n := by
    by_contra hm
    have hlt : m < n := by omega
    have he := hp.getElem (i := m) (by simp)
    simp [List.getElem_append, hlt] at he
    exact hne he.symm
  rw [hmn]

private lemma first_zero_levels {A : Type*} [Fintype A] [DecidableEq A]
    (zero one : A) (n : ℕ) :
    D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.level
      (firstZeroCode zero one) n =
      if n = 0 then ∅ else {List.replicate (n - 1) one ++ [zero]} := by
  classical
  open D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality in
  ext v
  simp only [level, mem_filter, words, mem_image, mem_univ, true_and,
    firstZeroCode, Set.mem_range]
  by_cases hn : n = 0
  · subst n
    simp only [ite_true, Finset.notMem_empty, iff_false]
    rintro ⟨⟨u, hu⟩, k, hk⟩
    have hlen := congrArg List.length (hu.trans hk.symm)
    simp only [u.2, List.length_append, List.length_replicate, List.length_singleton] at hlen
    omega
  · simp only [if_neg hn, mem_singleton]
    constructor
    · rintro ⟨⟨u, hu⟩, k, hk⟩
      have hlen := congrArg List.length hu
      rw [u.2] at hlen
      have hv : v.length = k + 1 := by rw [← hk]; simp
      have hn' : k = n - 1 := by omega
      simpa only [hn'] using hk.symm
    · intro hv
      have hlen : v.length = n := by rw [hv]; simp; omega
      exact ⟨⟨⟨v, hlen⟩, rfl⟩, n - 1, hv.symm⟩

private lemma first_zero_legal {A : Type*} [Fintype A] [DecidableEq A]
    (zero one : A) (hne : one ≠ zero) (b : ℕ → ℕ) (hb : ∀ n, 1 ≤ n → 1 ≤ b n) :
    D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.Legal b (firstZeroCode zero one) := by
  refine ⟨first_zero_prefix_free zero one hne, ?_, fun n => ?_⟩
  · rintro ⟨n, hn⟩
    have := congrArg List.length hn
    simp at this
  · rw [first_zero_levels]
    split_ifs with hn
    · simp
    · simp only [card_singleton]
      exact hb n (by omega)

/-- Hitting time of the actual first-zero prefix code; no matching prefix means infinity. -/
def codeTime {A : Type*} [DecidableEq A] (zero one : A) (x : ℕ → A) : ℝ≥0∞ :=
  ⨅ n : ℕ, if (∀ i < n, x i = one) ∧ x n = zero then (n + 1 : ℕ) else ∞

private lemma code_time_depth {A : Type*} [DecidableEq A] (zero one : A)
    (hne : one ≠ zero) (n : ℕ) (hn : 1 ≤ n) :
    codeTime zero one (depthPath zero one n) = (n : ℝ≥0∞) := by
  apply le_antisymm
  · apply iInf_le_of_le (n - 1)
    have hhit : (∀ i < n - 1, depthPath zero one n i = one) ∧
        depthPath zero one n (n - 1) = zero := by
      constructor
      · intro i hi
        simp only [depthPath, if_pos (by omega : i + 1 < n)]
      · simp only [depthPath, if_neg (by omega : ¬n - 1 + 1 < n)]
    rw [if_pos hhit]
    exact_mod_cast (show n - 1 + 1 ≤ n by omega)
  · apply le_iInf
    intro i
    split_ifs with hhit
    · have hi : n ≤ i + 1 := by
        by_contra h
        have hz := hhit.2
        rw [depthPath, if_pos (by omega : i + 1 < n)] at hz
        exact hne hz
      exact_mod_cast hi
    · exact le_top

private lemma measurable_codeTime {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [DecidableEq A] (zero one : A) :
    Measurable (codeTime zero one : (ℕ → A) → ℝ≥0∞) := by
  apply Measurable.iInf
  intro n
  have hcoord (i : ℕ) (a : A) : MeasurableSet {x : ℕ → A | x i = a} :=
    (measurable_pi_apply i : Measurable (fun x : ℕ → A => x i)) (measurableSet_singleton a)
  have hm : MeasurableSet {x : ℕ → A | (∀ i < n, x i = one) ∧ x n = zero} := by
    have heq : {x : ℕ → A | (∀ i < n, x i = one) ∧ x n = zero} =
        (⋂ i ∈ Set.Iio n, {x : ℕ → A | x i = one}) ∩ {x : ℕ → A | x n = zero} := by
      ext x
      simp
    rw [heq]
    exact (MeasurableSet.biInter (Set.to_countable (Set.Iio n))
      (fun i _ => hcoord i one)).inter (hcoord n zero)
  exact measurable_const.ite hm measurable_const

private lemma code_time_nohit {A : Type*} [DecidableEq A] (zero one : A) (x : ℕ → A) :
    codeTime zero one x = ∞ ↔ ∀ n, ¬((∀ i < n, x i = one) ∧ x n = zero) := by
  simp [codeTime, iInf_eq_top]

private lemma code_prefix_bridge {A : Type*} (zero one : A) (x : ℕ → A) (n : ℕ) :
    List.ofFn (fun i : Fin (n + 1) => x i) = List.replicate n one ++ [zero] ↔
      (∀ i < n, x i = one) ∧ x n = zero := by
  constructor
  · intro h
    constructor
    · intro i hi
      have he := List.getElem_of_eq h (i := i) (by simp; omega)
      simpa only [List.getElem_ofFn, List.getElem_append, List.length_replicate,
        dif_pos hi, List.getElem_replicate] using he
    · have he := List.getElem_of_eq h (i := n) (by simp)
      simpa only [List.getElem_ofFn, List.getElem_append, List.length_replicate,
        dif_neg (Nat.lt_irrefl n), Nat.sub_self, List.getElem_cons_zero] using he
  · rintro ⟨hprev, hzero⟩
    apply List.ext_getElem (by simp)
    intro i hi hj
    by_cases hin : i < n
    · simp only [List.getElem_ofFn, List.getElem_append, List.length_replicate,
        dif_pos hin, List.getElem_replicate, hprev i hin]
    · have hie : i = n := by simp only [List.length_ofFn] at hi; omega
      subst i
      simp only [List.getElem_ofFn, List.getElem_append, List.length_replicate,
        dif_neg (Nat.lt_irrefl n), Nat.sub_self, List.getElem_cons_zero, hzero]

private lemma atomic_values (t : ℕ → ℕ) (hs : StrictMono t) (ht : ∀ k, 2 ≤ t k) :
    atomicLaw t {1} = ENNReal.ofReal (1 - ∑' k, weight t k) ∧
    ∀ k, atomicLaw t {t k} = ENNReal.ofReal (weight t k) := by
  have hn (k : ℕ) : t k ≠ 1 := by have := ht k; omega
  constructor
  · simp [atomicLaw, Measure.sum_apply, hn]
  · intro k
    simp only [atomicLaw, Measure.add_apply, Measure.smul_apply, Measure.sum_apply _ (measurableSet_singleton _)]
    have hzero : Measure.dirac (1 : ℕ) {t k} = 0 := by simp [hn k, (hn k).symm]
    rw [hzero, smul_zero, zero_add]
    rw [tsum_eq_single k]
    · simp
    · intro j hj
      have hne : t j ≠ t k := fun he => hj (hs.injective he)
      simp [hne, hne.symm]

private lemma atomic_mean (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    1 ≤ (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ≤
      ENNReal.ofReal (1 + (1 / 4 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) ∧
    (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) < ∞ := by
  letI := atomic_probability t ht
  have hp (k : ℕ) : 0 ≤ weight t k := by unfold weight; positivity
  obtain ⟨hs, hmass, hm⟩ := weight_bounds t ht
  have hmoment : (∑' k, weight t k * (t k : ℝ)) =
      (1 / 4 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    have hn : (t k : ℝ) ≠ 0 := by
      exact_mod_cast (show t k ≠ 0 by have := ht k; omega)
    unfold weight
    field_simp
  have hformula : (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) =
      ENNReal.ofReal (1 - ∑' k, weight t k + ∑' k, weight t k * (t k : ℝ)) := by
    simp only [atomicLaw, lintegral_add_measure, lintegral_smul_measure,
      lintegral_sum_measure, lintegral_dirac, smul_eq_mul, Nat.cast_one, mul_one]
    rw [ENNReal.ofReal_add (by linarith) (tsum_nonneg (fun k => mul_nonneg (hp k) (Nat.cast_nonneg _))),
      ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hp k) (Nat.cast_nonneg _)) hm]
    apply congrArg (_ + ·)
    apply tsum_congr
    intro k
    rw [ENNReal.ofReal_mul (hp k), ENNReal.ofReal_natCast]
  have hlo : 1 ≤ (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) := by
    calc
      1 = ∫⁻ _n : ℕ, (1 : ℝ≥0∞) ∂atomicLaw t := by simp
      _ ≤ _ := lintegral_mono_ae (by
        filter_upwards [atomic_positive t ht] with n hn
        exact_mod_cast hn)
  refine ⟨hlo, ?_, ?_⟩
  · rw [hformula, hmoment]
    apply ENNReal.ofReal_le_ofReal
    have hsumpos : 0 ≤ ∑' k, weight t k := tsum_nonneg hp
    linarith
  · rw [hformula]
    exact ENNReal.ofReal_lt_top

private lemma atomic_rounded_infinite (S : Grid) (t : ℕ → ℕ)
    (ht : ∀ k, 2 ≤ t k)
    (hg : ∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (t k : ℝ) ≤ (round S (t k) : ℝ)) :
    (∫⁻ n : ℕ, (round S n : ℝ≥0∞) ∂atomicLaw t) = ∞ := by
  by_contra h
  apply atomic_not_integrable S t ht hg
  refine ⟨(measurable_of_countable _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun n => Nat.cast_nonneg (round S n)))]
  simpa only [ENNReal.ofReal_natCast] using (lt_top_iff_ne_top.2 h)

/-- The complete all-law criterion uses the actual least retained depth. -/
theorem sparse_grid_integrability (S : Grid) :
    ratio S = segmentRatio S ∧
    (∀ n, n ≤ round S n ∧ ∀ j, n ≤ S.depth j → round S n ≤ S.depth j) ∧
    (∀ j, round S (S.depth j) = S.depth j) ∧
    (ratio S < ∞ ↔
      (fun n : ℕ => (round S n : ℝ)) =O[atTop] (fun n => (n : ℝ))) ∧
    (ratio S < ∞ ↔ AllLaw.{u} S) := by
  refine ⟨ratio_eq_segmentRatio S,
    fun n => ⟨le_round S n, fun _ hj => round_le S hj⟩,
    round_depth S, (linear_iff_ratio S).symm.trans (linear_iff_bigO S), ?_⟩
  exact (linear_iff_ratio S).symm.trans
    ⟨linear_preserves S, allLaw_implies_linear S⟩

private lemma measurable_extendedRound (S : Grid) : Measurable (extendedRound S) := by
  exact measurable_const.ite (measurableSet_singleton ∞)
    ((measurable_of_countable (fun n : ℕ => (round S n : ℝ≥0∞))).comp
      measurable_id.ennreal_toReal.nat_floor)

private lemma extended_round_nat (S : Grid) (n : ℕ) :
    extendedRound S (n : ℝ≥0∞) = (round S n : ℝ≥0∞) := by
  simp [extendedRound]

private lemma prefix_pushforward {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [DecidableEq A] (zero one : A) (hne : one ≠ zero)
    (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    Measure.map (codeTime zero one) (prefixLaw zero one t) =
      Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (atomicLaw t) := by
  rw [prefixLaw, Measure.map_map (measurable_codeTime zero one) (measurable_depthPath zero one)]
  apply Measure.map_congr
  filter_upwards [atomic_positive t ht] with n hn
  exact code_time_depth zero one hne n hn

private lemma prefix_moments {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] [DecidableEq A] (S : Grid) (zero one : A) (hne : one ≠ zero)
    (t : ℕ → ℕ) (ht : ∀ k, 2 ≤ t k) :
    (∫⁻ x, codeTime zero one x ∂prefixLaw zero one t) =
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
    (∫⁻ x, extendedRound S (codeTime zero one x) ∂prefixLaw zero one t) =
      (∫⁻ n : ℕ, (round S n : ℝ≥0∞) ∂atomicLaw t) := by
  constructor
  · rw [prefixLaw, lintegral_map (measurable_codeTime zero one) (measurable_depthPath zero one)]
    apply lintegral_congr_ae
    filter_upwards [atomic_positive t ht] with n hn
    exact code_time_depth zero one hne n hn
  · rw [prefixLaw, lintegral_map
      (show Measurable (fun x : ℕ → A => extendedRound S (codeTime zero one x)) from
        (measurable_extendedRound S).comp (measurable_codeTime zero one))
      (measurable_depthPath zero one)]
    apply lintegral_congr_ae
    filter_upwards [atomic_positive t ht] with n hn
    rw [code_time_depth zero one hne n hn, extended_round_nat]

/-- The source's one common law, including exact masses, both extended moments,
and its actual prefix-code realization over every suitable finite alphabet. -/
theorem common_law_prefix_witness (S : Grid) (h : ratio S = ∞) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      (∀ k, 2 ≤ t k) ∧
      (∀ k : ℕ, (k + 1 : ℝ) ^ 3 * (t k : ℝ) ≤ (round S (t k) : ℝ)) ∧
      IsProbabilityMeasure (atomicLaw t) ∧
      (∑' k, weight t k) ≤ 1 / 4 ∧
      atomicLaw t {1} = ENNReal.ofReal (1 - ∑' k, weight t k) ∧
      (∀ k, atomicLaw t {t k} = ENNReal.ofReal (weight t k)) ∧
      1 ≤ (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ≤
        ENNReal.ofReal (1 + (1 / 4 : ℝ) * ∑' k : ℕ, 1 / (k + 1 : ℝ) ^ 2) ∧
      (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) < ∞ ∧
      (∫⁻ n : ℕ, (round S n : ℝ≥0∞) ∂atomicLaw t) = ∞ ∧
      ∀ (A : Type u) [Fintype A] [DecidableEq A] [MeasurableSpace A]
        [MeasurableSingletonClass A] (zero one : A), one ≠ zero →
        (∀ n, codeTime zero one (depthPath zero one (n + 1)) = (n + 1 : ℕ)) ∧
        (∀ x, codeTime zero one x = ∞ ↔
          ∀ n, ¬((∀ i < n, x i = one) ∧ x n = zero)) ∧
        (∀ (x : ℕ → A) (n : ℕ), List.ofFn (fun i : Fin (n + 1) => x i) =
            List.replicate n one ++ [zero] ↔ (∀ i < n, x i = one) ∧ x n = zero) ∧
        (∀ n, (D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.level
          (firstZeroCode zero one) (n + 1)).card = 1) ∧
        (∀ (b : ℕ → ℕ), (∀ n, 1 ≤ n → 1 ≤ b n) →
          D5.S0.Computability.Coding.DepthBudgetIidGreedyOptimality.Legal b
            (firstZeroCode zero one)) ∧
        IsProbabilityMeasure (prefixLaw zero one t) ∧
        Measure.map (codeTime zero one) (prefixLaw zero one t) =
          Measure.map (fun n : ℕ => (n : ℝ≥0∞)) (atomicLaw t) ∧
        (∫⁻ x, codeTime zero one x ∂prefixLaw zero one t) =
          (∫⁻ n : ℕ, (n : ℝ≥0∞) ∂atomicLaw t) ∧
        (∫⁻ x, extendedRound S (codeTime zero one x) ∂prefixLaw zero one t) = ∞ := by
  have hn : ¬LinearBound S := by
    intro hb
    have := (linear_iff_ratio S).1 hb
    simpa only [h, lt_self_iff_false] using this
  obtain ⟨t, hs, ht, hg⟩ := exists_bad_depths S hn
  obtain ⟨hvone, hv⟩ := atomic_values t hs ht
  obtain ⟨hlo, hupper, hfinite⟩ := atomic_mean t ht
  have hinfinite := atomic_rounded_infinite S t ht hg
  refine ⟨t, hs, ht, hg, atomic_probability t ht, (weight_bounds t ht).2.1,
    hvone, hv, hlo, hupper, hfinite, hinfinite, ?_⟩
  intro A _ _ _ _ zero one hne
  refine ⟨fun n => code_time_depth zero one hne (n + 1) (by omega),
    code_time_nohit zero one, code_prefix_bridge zero one, ?_,
    first_zero_legal zero one hne, ?_, prefix_pushforward zero one hne t ht,
    (prefix_moments S zero one hne t ht).1, ?_⟩
  · intro n
    rw [first_zero_levels, if_neg (by omega)]
    simp
  · letI := atomic_probability t ht
    change IsProbabilityMeasure (Measure.map (depthPath zero one) (atomicLaw t))
    exact inferInstance
  · exact (prefix_moments S zero one hne t ht).2.trans hinfinite

#print axioms sparse_grid_integrability
#print axioms common_law_prefix_witness

end D5.S3.Observer.Budget.SparseGridIntegrability
