/- GID: D5/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/Learning/RawCorrelationMomentIdentities
   mirror-E: none(waiver:unbounded-symbolic-estimate)
   anchors: []
   utility: none
   digest: Actual heterogeneous window records have a diverging conditional nonzero count. -/

import D5.S3.Arith.AbsoluteValues.Heights.Gelfond
import D5.S3.Arith.GoldenPell
import D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic
import Mathlib.Topology.Order.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

noncomputable section
attribute [local instance] Classical.propDecidable
open Filter
open scoped BigOperators Topology


namespace D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities

namespace Scale

def sampleLength (rho a K : ℝ) : ℕ := ⌈K / (a ^ 2 * rho ^ 2)⌉₊

/-- The rounded sample count times rho squared tends to the prescribed constant. -/
theorem scaled_length (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun rho => (sampleLength rho a K : ℝ) * rho ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (K / a ^ 2)) := by
  have ha0 : a ≠ 0 := ne_of_gt ha
  have id0 : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have low : ∀ᶠ rho : ℝ in 𝓝[>] 0,
      K / a ^ 2 ≤ (sampleLength rho a K : ℝ) * rho ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with rho hrho
    have hr : 0 < rho := hrho
    have h := mul_le_mul_of_nonneg_right (Nat.le_ceil (K / (a ^ 2 * rho ^ 2)))
      (sq_nonneg rho)
    have heq : K / (a ^ 2 * rho ^ 2) * rho ^ 2 = K / a ^ 2 := by field_simp
    rwa [heq] at h
  have high : ∀ᶠ rho : ℝ in 𝓝[>] 0,
      (sampleLength rho a K : ℝ) * rho ^ 2 ≤ K / a ^ 2 + rho ^ 2 := by
    filter_upwards [self_mem_nhdsWithin] with rho hrho
    have hr : 0 < rho := hrho
    have h := mul_le_mul_of_nonneg_right
      (Nat.ceil_lt_add_one (by positivity : 0 ≤ K / (a ^ 2 * rho ^ 2))).le (sq_nonneg rho)
    have heq : (K / (a ^ 2 * rho ^ 2) + 1) * rho ^ 2 = K / a ^ 2 + rho ^ 2 := by field_simp <;> ring
    rwa [heq] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (by simpa using (tendsto_const_nhds.add (id0.pow 2) : Tendsto (fun rho : ℝ => K / a ^ 2 + rho ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (K / a ^ 2 + 0 ^ 2))))
    low high

/-- At the target sample scale, the expected reverse-event count tends to zero. -/
theorem reverse_negligible (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun rho => (sampleLength rho a K : ℝ) * 12 * rho ^ 3)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have h := (scaled_length a K ha hK).mul
    ((tendsto_id.mono_left nhdsWithin_le_nhds).const_mul (12 : ℝ))
  simpa only [mul_zero, zero_mul] using h.congr (fun rho => by dsimp; ring)

/-- All records avoid the reverse event with probability tending to one. -/
theorem clean_probability (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun rho => (1 - 12 * rho ^ 3) ^ (sampleLength rho a K))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have low : ∀ᶠ rho : ℝ in 𝓝[>] 0,
      1 - (sampleLength rho a K : ℝ) * 12 * rho ^ 3 ≤
        (1 - 12 * rho ^ 3) ^ (sampleLength rho a K) := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))]
      with rho hrho hr8
    have hr : 0 < rho := hrho
    have hc : rho ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hr.le hr8.le 3
    have hb : 0 ≤ 1 - 12 * rho ^ 3 := by norm_num at hc; nlinarith
    have h := one_add_mul_sub_le_pow (by linarith : -1 ≤ 1 - 12 * rho ^ 3)
      (sampleLength rho a K)
    nlinarith
  have high : ∀ᶠ rho : ℝ in 𝓝[>] 0,
      (1 - 12 * rho ^ 3) ^ (sampleLength rho a K) ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))]
      with rho hrho hr8
    have hr : 0 < rho := hrho
    have hc : rho ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hr.le hr8.le 3
    apply pow_le_one₀
    · norm_num at hc; nlinarith
    · have : 0 ≤ 12 * rho ^ 3 := by positivity
      linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (by simpa using tendsto_const_nhds.sub (reverse_negligible a K ha hK))
    tendsto_const_nhds low high

def activeProbability (rho a : ℝ) : ℝ :=
  ((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)

/-- The expected conditional nonzero count tends to infinity. -/
theorem active_mean_diverges (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun rho => (sampleLength rho a K : ℝ) * activeProbability rho a)
      (𝓝[>] (0 : ℝ)) atTop := by
  have id0 : Tendsto (fun rho : ℝ => rho) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun rho : ℝ =>
      ((8 + a) / 12) * 2 * (1 - 3 * rho) * (1 - 2 * rho) / (1 - 12 * rho ^ 3))
      (𝓝[>] (0 : ℝ)) (𝓝 (((8 + a) / 12) * 2)) := by
    have hcont : ContinuousAt (fun rho : ℝ =>
        ((8 + a) / 12) * 2 * (1 - 3 * rho) * (1 - 2 * rho) / (1 - 12 * rho ^ 3)) (0 : ℝ) := by
      fun_prop (disch := norm_num)
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hh := (scaled_length a K ha hK).mul hg
  have hc : 0 < (K / a ^ 2) * (((8 + a) / 12) * 2) := by positivity
  have ht := hh.pos_mul_atTop hc tendsto_inv_nhdsGT_zero
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with rho hrho
  have hr : rho ≠ 0 := ne_of_gt (show 0 < rho from hrho)
  dsimp [activeProbability]
  field_simp
  <;> ring

end Scale

namespace FiniteTail

def count {α : Type*} {m : ℕ} (b : α → ℕ) (w : Fin m → α) : ℕ := ∑ i, b (w i)
def tail {α : Type*} [Fintype α] (q : α → ℝ) (b : α → ℕ) (m N : ℕ) : ℝ :=
  ∑ w : Fin m → α, if count b w ≤ N then ∏ i, q (w i) else 0

/-- The count Laplace transform factors over independent finite records. -/
theorem laplace_product {α : Type*} [Fintype α] (q : α → ℝ)
    (b : α → ℕ) (m : ℕ) :
    (∑ w : Fin m → α, (∏ i, q (w i)) * Real.exp (-(count b w : ℝ))) =
      (∑ a, q a * Real.exp (-(b a : ℝ))) ^ m := by
  classical
  simp only [count, Nat.cast_sum, ← Finset.sum_neg_distrib, Real.exp_sum,
    ← Finset.prod_mul_distrib]
  exact (Fintype.sum_pow (fun a => q a * Real.exp (-(b a : ℝ))) m).symm

/-- A fixed-count lower tail is bounded by its exponential transform. -/
theorem tail_laplace_bound {α : Type*} [Fintype α] (q : α → ℝ)
    (b : α → ℕ) (hq : ∀ a, 0 ≤ q a) (m N : ℕ) :
    tail q b m N ≤ Real.exp (N : ℝ) * (∑ a, q a * Real.exp (-(b a : ℝ))) ^ m := by
  unfold tail
  rw [← laplace_product, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro w hw
  have hp : 0 ≤ ∏ i, q (w i) := Finset.prod_nonneg (fun i hi => hq (w i))
  by_cases h : count b w ≤ N
  · simp only [tail, if_pos h]
    have he : 1 ≤ Real.exp (N : ℝ) * Real.exp (-(count b w : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      have hn : (count b w : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
      linarith
    nlinarith
  · simp only [if_neg h]
    positivity

/-- The finite-product lower tail has an exponential upper bound. -/
theorem tail_exponential {α : Type*} [Fintype α] (q : α → ℝ)
    (b : α → ℕ) (hq : ∀ a, 0 ≤ q a) (m N : ℕ) (p : ℝ)
    (hlap : (∑ a, q a * Real.exp (-(b a : ℝ))) = 1 - p + p * Real.exp (-1)) :
    tail q b m N ≤ Real.exp (N : ℝ) * Real.exp (-((1 - Real.exp (-1)) * (m : ℝ) * p)) := by
  have hl := tail_laplace_bound q b hq m N
  rw [hlap] at hl
  have hb : 0 ≤ 1 - p + p * Real.exp (-1) := by
    rw [← hlap]
    exact Finset.sum_nonneg (fun a ha => mul_nonneg (hq a) (Real.exp_pos _).le)
  have he : 1 - p + p * Real.exp (-1) ≤ Real.exp (-((1 - Real.exp (-1)) * p)) := by
    have h := Real.add_one_le_exp (-((1 - Real.exp (-1)) * p))
    nlinarith
  have hp := pow_le_pow_left₀ hb he m
  rw [← Real.exp_nat_mul] at hp
  have heq : (m : ℝ) * (-((1 - Real.exp (-1)) * p)) = -((1 - Real.exp (-1)) * (m : ℝ) * p) := by ring
  rw [heq] at hp
  exact hl.trans (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le)

/-- Diverging activation means force every fixed lower tail to vanish. -/
theorem escapes {α ι : Type*} [Fintype α] (l : Filter ι) (q : ι → α → ℝ)
    (b : α → ℕ) (n : ι → ℕ) (p : ι → ℝ)
    (hq : ∀ᶠ t in l, ∀ a, 0 ≤ q t a)
    (hlap : ∀ᶠ t in l, (∑ a, q t a * Real.exp (-(b a : ℝ))) = 1 - p t + p t * Real.exp (-1))
    (hmean : Tendsto (fun t => (n t : ℝ) * p t) l atTop) (N : ℕ) :
    Tendsto (fun t => tail (q t) b (n t) N) l (𝓝 0) := by
  have hc : 0 < 1 - Real.exp (-1) := by
    have : Real.exp (-1) < Real.exp 0 := Real.exp_lt_exp.mpr (by norm_num)
    simpa using sub_pos.mpr this
  have lim := (Real.tendsto_exp_atBot.comp
    (hmean.const_mul_atTop_of_neg (neg_lt_zero.mpr hc))).const_mul (Real.exp (N : ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using lim)
  · filter_upwards [hq] with t ht
    unfold tail
    apply Finset.sum_nonneg
    intro w hw
    split_ifs
    · exact Finset.prod_nonneg (fun i hi => ht _)
    · exact le_rfl
  · filter_upwards [hq, hlap] with t ht hl
    have h := tail_exponential (q t) b ht (n t) N (p t) hl
    have heq : -((1 - Real.exp (-1)) * (n t : ℝ) * p t) =
        (Real.exp (-1) - 1) * ((n t : ℝ) * p t) := by ring
    simpa only [heq] using h

def expectation {α : Type*} [Fintype α] (q : α → ℝ) (b : α → ℕ)
    (m : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ w : Fin m → α, (∏ i, q (w i)) * f (count b w)

/-- A cutoff separates bounded small-count and uniformly small large-count contributions. -/
theorem expectation_cutoff {α : Type*} [Fintype α] (q : α → ℝ)
    (b : α → ℕ) (hq : ∀ a, 0 ≤ q a) (hprob : ∑ a, q a = 1)
    (m N : ℕ) (f : ℕ → ℝ) (hf : ∀ j, f j ≤ 1) (eps : ℝ)
    (heps : 0 ≤ eps) (hfar : ∀ j, N < j → f j ≤ eps) :
    expectation q b m f ≤ tail q b m N + eps := by
  have htotal : (∑ w : Fin m → α, ∏ i, q (w i)) = 1 := by
    rw [← Fintype.sum_pow, hprob, one_pow]
  unfold expectation tail
  calc
    _ ≤ ∑ w : Fin m → α,
        ((if count b w ≤ N then ∏ i, q (w i) else 0) + (∏ i, q (w i)) * eps) := by
      apply Finset.sum_le_sum
      intro w hw
      have hp : 0 ≤ ∏ i, q (w i) := Finset.prod_nonneg (fun i hi => hq _)
      by_cases h : count b w ≤ N
      · simp only [if_pos h]
        have hx := mul_le_mul_of_nonneg_left (hf (count b w)) hp
        nlinarith
      · simp only [if_neg h, zero_add]
        exact mul_le_mul_of_nonneg_left (hfar _ (Nat.lt_of_not_ge h)) hp
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, htotal, one_mul]

/-- A bounded vanishing count observable has vanishing expectation when counts escape. -/
theorem expectation_vanishes {α ι : Type*} [Fintype α] (l : Filter ι)
    (q : ι → α → ℝ) (b : α → ℕ) (n : ι → ℕ) (f : ℕ → ℝ)
    (hq : ∀ᶠ t in l, ∀ a, 0 ≤ q t a) (hprob : ∀ᶠ t in l, ∑ a, q t a = 1)
    (hf0 : ∀ j, 0 ≤ f j) (hf1 : ∀ j, f j ≤ 1)
    (hf : Tendsto f atTop (𝓝 0))
    (htails : ∀ N, Tendsto (fun t => tail (q t) b (n t) N) l (𝓝 0)) :
    Tendsto (fun t => expectation (q t) b (n t) f) l (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro z hz
    filter_upwards [hq] with t ht
    have he : 0 ≤ expectation (q t) b (n t) f :=
      Finset.sum_nonneg (fun w hw => mul_nonneg (Finset.prod_nonneg (fun i hi => ht _)) (hf0 _))
    exact hz.trans_le he
  · intro eps heps
    obtain ⟨N, hN⟩ := (eventually_atTop.1 (hf.eventually (gt_mem_nhds (half_pos heps))))
    filter_upwards [hq, hprob, (htails N).eventually (gt_mem_nhds (half_pos heps))]
      with t ht hpr htail
    have hbd := expectation_cutoff (q t) b ht hpr (n t) N f hf1
      (eps / 2) (half_pos heps).le (fun j hj => (hN j hj.le).le)
    linarith

end FiniteTail

namespace Law
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation (extremal)

abbrev Record := Window × Window × Window × Window × Fin 3

set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.2.1, w.2.2.1, w.2.2.2.1])

def biased (rho : ℝ) : Window → ℝ
  | .high => 1 - 4 * rho
  | _ => rho

def channel (a : ℝ) (c y : Fin 3) : ℝ :=
  if y = 1 then (4 - a) / 12
  else if c = 1 then (8 + a) / 24
  else if c = y then (4 + 2 * a) / 12 else (4 - a) / 12

def score (w : Record) : ℤ :=
  ((w.2.2.2.2.val : ℤ) - 1) * (((trueClass w).val : ℤ) - ((rivalClass w).val : ℤ))
def reverse (w : Record) : Prop :=
  last w.1 = false ∧ last w.2.1 = true ∧ first w.2.2.1 = true

def recordMass (rho a : ℝ) (w : Record) : ℝ :=
  biased rho w.1 * extremal rho w.2.1 * extremal rho w.2.2.1 *
    extremal rho w.2.2.2.1 * channel a (trueClass w) w.2.2.2.2

noncomputable def misorder (rho a : ℝ) (m : ℕ) : ℝ :=
  ∑ w : Fin m → Record,
    if (∑ i, score (w i)) < 0 then ∏ i, recordMass rho a (w i) else 0

def sumWindow (f : Window → ℝ) : ℝ :=
  f .zero + f .low + f .middle + f .ends + f .high

def oneSum (f : Record → ℝ) : ℝ :=
  sumWindow fun w1 => sumWindow fun w2 => sumWindow fun w3 => sumWindow fun w4 =>
    f (w1,w2,w3,w4,0) + f (w1,w2,w3,w4,1) + f (w1,w2,w3,w4,2)

def cleanMass (rho a : ℝ) (s : ℤ) : ℝ := by
  classical
  exact oneSum (fun w => if ¬ reverse w ∧ score w = s then recordMass rho a w else 0)

/-- The explicit five-symbol record sum equals the complete finite sum. -/
theorem one_sum_eq_sum (f : Record → ℝ) : oneSum f = ∑ w, f w := by
  classical
  have win (g : Window → ℝ) : (∑ w, g w) = sumWindow g := by
    change (∑ w ∈ ({Window.zero, Window.low, Window.middle, Window.ends, Window.high} : Finset Window), g w) = _
    simp [sumWindow, add_assoc]
  simp only [Fintype.sum_prod_type, win, Fin.sum_univ_three, oneSum]

/-- The actual window-label mass has total one. -/
theorem total_mass (rho a : ℝ) : (∑ w, recordMass rho a w) = 1 := by
  rw [← one_sum_eq_sum]
  simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, recordMass, biased, extremal, channel,
    GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]
  ring

/-- Excluding the reverse event removes exactly its cubic mass. -/
theorem clean_total (rho a : ℝ) :
    (∑ w : Record, if ¬ reverse w then recordMass rho a w else 0) = 1 - 12 * rho ^ 3 := by
  classical
  rw [← one_sum_eq_sum]
  simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, reverse, recordMass, biased, extremal, channel,
    GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first, LiteralWindowEnd.last]
  ring

/-- The two nonzero score masses are equal after excluding the reverse event. -/
theorem clean_signs (rho a : ℝ) :
    cleanMass rho a 1 = (8 + a) / 12 * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / 2 ∧
    cleanMass rho a (-1) = (8 + a) / 12 * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / 2 := by
  constructor <;>
    simp (config := { maxSteps := 1000000 }) [cleanMass, oneSum, sumWindow, reverse, score, recordMass, biased, extremal, channel, GarbledPosteriorRootGap.teacher, LiteralWindowEnd.first,
      LiteralWindowEnd.last] <;> ring

def cleanRecordMass (rho a : ℝ) (w : Record) : ℝ := by
  classical
  exact if ¬ reverse w then recordMass rho a w / (1 - 12 * rho ^ 3) else 0

def cleanSampleMass (rho a : ℝ) {m : ℕ} (w : Fin m → Record) : ℝ := by
  classical
  exact (if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho a (w i) else 0) /
    (1 - 12 * rho ^ 3) ^ m

/-- Conditioning all records on avoiding the reverse event preserves their product form. -/
theorem clean_sample_factor (rho a : ℝ) (m : ℕ) (w : Fin m → Record) :
    cleanSampleMass rho a w = ∏ i, cleanRecordMass rho a (w i) := by
  classical
  by_cases h : ∀ i, ¬ reverse (w i)
  · simp [cleanSampleMass, cleanRecordMass, h, Finset.prod_div_distrib]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    simp only [cleanSampleMass, if_neg h, zero_div]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [cleanRecordMass, hi]

/-- The simultaneous clean event has the exact product probability. -/
theorem all_clean_mass (rho a : ℝ) (m : ℕ) :
    (∑ w : Fin m → Record, if ∀ i, ¬ reverse (w i) then
      ∏ i, recordMass rho a (w i) else 0) = (1 - 12 * rho ^ 3) ^ m := by
  classical
  have eqProd (w : Fin m → Record) :
      (if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho a (w i) else 0) =
        ∏ i, (if ¬ reverse (w i) then recordMass rho a (w i) else 0) :=
    by
      have h := (Fintype.prod_ite_zero (p := fun i => ¬ reverse (w i))
        (f := fun i => recordMass rho a (w i))).symm
      by_cases hw : ∀ i, ¬ reverse (w i)
      · simpa only [if_pos hw] using h
      · simpa only [if_neg hw] using h
  simp_rw [eqProd]
  have h := (Fintype.sum_pow (fun w : Record =>
    if ¬ reverse w then recordMass rho a w else 0) m).symm
  simpa only [clean_total] using h

end Law

namespace Law
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation (extremal)
/-- The single-record conditioning event has positive mass in the legal rho range. -/
theorem clean_denominator_pos (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    0 < 1 - 12 * rho ^ 3 := by
  have hc : rho ^ 3 ≤ (1 / 8 : ℝ) ^ 3 := pow_le_pow_left₀ hr.le hr8 3
  norm_num at hc
  linarith

/-- Every actual complete-record mass is nonnegative in the legal parameter range. -/
theorem record_mass_nonneg (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record) : 0 ≤ recordMass rho a w := by
  have hb (v : Window) : 0 ≤ biased rho v := by cases v <;> simp [biased] <;> linarith
  have he (v : Window) : 0 ≤ extremal rho v := by cases v <;> simp [extremal] <;> linarith
  have hc (c y : Fin 3) : 0 ≤ channel a c y := by
    unfold channel
    split_ifs <;> linarith
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (hb _) (he _)) (he _)) (he _)) (hc _ _)

/-- The conditioned complete-record mass is nonnegative. -/
theorem clean_record_mass_nonneg (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8)
    (ha : 0 < a) (ha1 : a ≤ 1) (w : Record) : 0 ≤ cleanRecordMass rho a w := by
  by_cases h : reverse w
  · simp [cleanRecordMass, h]
  · simp only [cleanRecordMass, if_pos h]
    exact div_nonneg (record_mass_nonneg rho a hr hr8 ha ha1 w)
      (clean_denominator_pos rho hr hr8).le

/-- The conditioned complete-record law has total one. -/
theorem clean_record_mass_total (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    (∑ w, cleanRecordMass rho a w) = 1 := by
  have ht (w : Record) : cleanRecordMass rho a w =
      (if ¬ reverse w then recordMass rho a w else 0) / (1 - 12 * rho ^ 3) := by
    unfold cleanRecordMass
    split_ifs <;> simp
  simp_rw [ht]
  rw [← Finset.sum_div, clean_total, div_self (clean_denominator_pos rho hr hr8).ne']

/-- The actual raw-score difference takes only the three integer values minus one, zero and one. -/
theorem score_range (w : Record) : score w = -1 ∨ score w = 0 ∨ score w = 1 := by
  rcases w with ⟨w1,w2,w3,w4,y⟩
  fin_cases y <;>
    simp [score, GarbledPosteriorRootGap.teacher]
      <;> split_ifs <;> norm_num

def cleanScore (rho a : ℝ) (s : ℤ) : ℝ :=
  ∑ w, if score w = s then cleanRecordMass rho a w else 0

/-- Conditioned score masses are the corresponding restricted masses divided by the clean mass. -/
theorem clean_score_eq (rho a : ℝ) (s : ℤ) :
    cleanScore rho a s = cleanMass rho a s / (1 - 12 * rho ^ 3) := by
  unfold cleanScore cleanMass
  rw [one_sum_eq_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro w hw
  unfold cleanRecordMass
  by_cases hr : reverse w <;> by_cases hs : score w = s <;> simp [hr, hs]

/-- The positive and negative conditional score masses both equal half the activity probability. -/
theorem clean_score_signs (rho a : ℝ) :
    cleanScore rho a 1 = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2 ∧
    cleanScore rho a (-1) = (((8 + a) / 12) * (2 * rho * (1 - 3 * rho) * (1 - 2 * rho)) / (1 - 12 * rho ^ 3)) / 2 := by
  rw [clean_score_eq, clean_score_eq, (clean_signs rho a).1, (clean_signs rho a).2]
  constructor <;> ring

/-- The three conditional score categories partition the record mass. -/
theorem clean_score_partition (rho a : ℝ) :
    cleanScore rho a (-1) + cleanScore rho a 0 + cleanScore rho a 1 =
      ∑ w, cleanRecordMass rho a w := by
  unfold cleanScore
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro w hw
  rcases score_range w with hs | hs | hs <;> simp [hs]

def nonzero (w : Record) : ℕ := if score w = 0 then 0 else 1

/-- The exact conditional nonzero mass agrees with the activity probability. -/
theorem clean_active_mass (rho a : ℝ) :
    (∑ w, if score w ≠ 0 then cleanRecordMass rho a w else 0) =
      Scale.activeProbability rho a := by
  have hp : (∑ w, if score w ≠ 0 then cleanRecordMass rho a w else 0) =
      cleanScore rho a (-1) + cleanScore rho a 1 := by
    unfold cleanScore
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    rcases score_range w with hs | hs | hs <;> simp [hs]
  rw [hp, (clean_score_signs rho a).1, (clean_score_signs rho a).2]
  unfold Scale.activeProbability
  ring

/-- The actual conditional nonzero indicator has the Bernoulli Laplace transform. -/
theorem laplace_actual (rho a : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    (∑ w, cleanRecordMass rho a w * Real.exp (-(nonzero w : ℝ))) =
      1 - Scale.activeProbability rho a + Scale.activeProbability rho a * Real.exp (-1) := by
  have term (w : Record) : cleanRecordMass rho a w * Real.exp (-(nonzero w : ℝ)) =
      cleanRecordMass rho a w +
        (if score w ≠ 0 then cleanRecordMass rho a w else 0) * (Real.exp (-1) - 1) := by
    unfold nonzero
    by_cases h : score w = 0 <;> simp [h] <;> ring
  simp_rw [term]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, clean_record_mass_total rho a hr hr8,
    clean_active_mass]
  ring

/-- The probability of simultaneously excluding all reverse events tends to one. -/
theorem all_clean_limit (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun rho => ∑ w : Fin (Scale.sampleLength rho a K) → Record,
      if ∀ i, ¬ reverse (w i) then ∏ i, recordMass rho a (w i) else 0)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  simpa only [all_clean_mass] using Scale.clean_probability a K ha hK

/-- Every fixed nonzero-count lower tail vanishes in the actual conditional product law. -/
theorem nonzero_count_diverges (a K : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (hK : 0 < K)
    (N : ℕ) :
    Tendsto (fun rho => FiniteTail.tail (cleanRecordMass rho a) nonzero
      (Scale.sampleLength rho a K) N) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have small : ∀ᶠ rho : ℝ in 𝓝[>] (0 : ℝ), 0 < rho ∧ rho ≤ 1 / 8 := by
    filter_upwards [self_mem_nhdsWithin,
      (tendsto_id.mono_left nhdsWithin_le_nhds : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0)).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ)<1 / 8))] with rho hr hr8
    exact ⟨hr, hr8.le⟩
  apply FiniteTail.escapes (𝓝[>] (0 : ℝ)) (fun rho => cleanRecordMass rho a)
    nonzero (fun rho => Scale.sampleLength rho a K)
    (fun rho => Scale.activeProbability rho a)
  · filter_upwards [small] with rho hr
    exact clean_record_mass_nonneg rho a hr.1 hr.2 ha ha1
  · filter_upwards [small] with rho hr
    exact laplace_actual rho a hr.1 hr.2
  · exact Scale.active_mean_diverges a K ha hK

end Law

namespace Pushforward

/-- Coordinatewise pushforward of a finite product law is the product of the coordinate pushforwards. -/
theorem product_pushforward {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (q : β → ℝ)
    (hq : ∀ b, q b = ∑ a, if f a = b then p a else 0)
    (m : ℕ) (F : (Fin m → β) → ℝ) :
    (∑ x : Fin m → α, F (fun i => f (x i)) * ∏ i, p (x i)) =
      ∑ y : Fin m → β, F y * ∏ i, q (y i) := by
  classical
  simp_rw [hq]
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp_rw [Fintype.prod_ite_zero]
  have heq (y : Fin m → β) : (∀ i, f (x i) = y i) ↔ y = fun i => f (x i) := by
    constructor
    · intro h
      funext i
      exact (h i).symm
    · rintro rfl
      exact fun i => rfl
  simp_rw [heq, mul_ite, mul_zero]
  simp

end Pushforward

namespace Binomial

def fairTie (j : ℕ) : ℝ := if j % 2 = 0 then (j.choose (j / 2) : ℝ) / (2 : ℝ) ^ j else 0

/-- Fair-sign tie coefficients are nonnegative. -/
theorem fair_tie_nonneg (j : ℕ) : 0 ≤ fairTie j := by
  unfold fairTie
  split_ifs <;> positivity

/-- The frozen central-binomial inequality bounds the square of the fair-sign tie coefficient. -/
theorem fair_tie_square_bound (j : ℕ) : (fairTie j) ^ 2 ≤ 1 / ((j : ℝ) + 1) := by
  unfold fairTie
  split_ifs
  · have h := Nat.choose_middle_sq_mul_le j
    have h' : (j.choose (j / 2) : ℝ) ^ 2 * ((j : ℝ) + 1) ≤ (4 : ℝ) ^ j := by exact_mod_cast h
    rw [div_pow, div_le_div_iff₀ (by positivity : (0 : ℝ)<((2 : ℝ) ^ j) ^ 2)
      (by positivity : (0 : ℝ)<(j : ℝ) + 1)]
    have hp : ((2 : ℝ) ^ j) ^ 2 = (4 : ℝ) ^ j := by
      rw [← pow_mul, Nat.mul_comm j 2, pow_mul]
      norm_num
    simpa only [one_mul, hp] using h'
  · simp
    positivity

/-- Fair-sign tie coefficients tend to zero with the number of signs. -/
theorem fair_tie_vanishes : Tendsto fairTie atTop (𝓝 (0 : ℝ)) := by
  have lim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [Real.sqrt_zero] using lim.sqrt)
    fair_tie_nonneg (fun j => Real.le_sqrt_of_sq_le (fair_tie_square_bound j))


end Binomial

namespace FairWalk

local notation "boolSubset" α =>
  (Equiv.trans (Equiv.piCongrRight (fun _ : α => Equiv.symm Equiv.propEquivBool))
    (Equiv.symm (Fintype.finsetEquivSet (α := α))))

local notation "sign" => (fun b : Bool => D5.S3.Arith.GoldenPell.signedInt (!b) 1)

/-- A fair-sign sum is twice the positive-sign subset size minus the domain size. -/
theorem signed_sum_subset {α : Type*} [Fintype α] (s : Finset α) :
    (∑ i, sign ((boolSubset α).symm s i)) = 2 * (s.card : ℤ) - (Fintype.card α : ℤ) := by
  have term (i : α) : sign ((boolSubset α).symm s i) =
      (if i ∈ s then (2 : ℤ) else 0) - 1 := by
    simp only [Equiv.symm_trans_apply, Equiv.symm_symm]
    by_cases hi : i ∈ s <;>
      simp [D5.S3.Arith.GoldenPell.signedInt, Equiv.piCongrRight,
        Equiv.propEquivBool, hi]
    all_goals simpa only [Equiv.symm, Fintype.finsetEquivSet] using hi
  simp_rw [term]
  simp [Finset.sum_sub_distrib, Finset.sum_ite_mem, mul_comm]

noncomputable def fairTie {α : Type*} [Fintype α] : ℝ :=
  ∑ u : α → Bool, if (∑ i, sign (u i)) = 0 then (1 / 2 : ℝ) ^ (Fintype.card α) else 0

/-- The exact fair-sign tie mass is its central-binomial coefficient at even lengths. -/
theorem fair_tie_formula (α : Type*) [Fintype α] :
    fairTie (α := α) = Binomial.fairTie (Fintype.card α) := by
  classical
  unfold fairTie
  rw [← (boolSubset α).symm.sum_comp]
  simp_rw [signed_sum_subset]
  let n := Fintype.card α
  by_cases he : n % 2 = 0
  · have hi (s : Finset α) : 2 * (s.card : ℤ) - (Fintype.card α : ℤ)=0 ↔ s.card=n / 2 := by
      dsimp [n] at *
      omega
    simp_rw [hi]
    have hc : (Finset.univ.filter (fun s : Finset α => s.card=n / 2)).card = n.choose (n / 2) := by
      have hset : Finset.univ.filter (fun s : Finset α => s.card=n / 2) =
          Finset.univ.powersetCard (n / 2) := by ext s; simp
      rw [hset, Finset.card_powersetCard, Finset.card_univ]
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul, hc]
    unfold Binomial.fairTie
    rw [if_pos he]
    simp [one_div_pow, div_eq_mul_inv, n]
  · have hi (s : Finset α) : 2 * (s.card : ℤ) - (Fintype.card α : ℤ) ≠ 0 := by
      dsimp [n] at *
      omega
    simp_rw [if_neg (hi _)]
    simp [Binomial.fairTie, he, n]

end FairWalk

namespace ActiveFair
open FairWalk
local notation "sign" => (fun b : Bool => D5.S3.Arith.GoldenPell.signedInt (!b) 1)

/-- Inactive fair signs integrate out and leave the tie coefficient of the active set. -/
theorem active_fair_tie {α : Type*} [Fintype α] (a : α → Bool) :
    (∑ u : α → Bool, if (∑ i, if a i then sign (u i) else 0) = 0 then
      (1 / 2 : ℝ) ^ (Fintype.card α) else 0) =
      Binomial.fairTie (Fintype.card {i : α // a i = true}) := by
  classical
  let A := {i : α // a i = true}
  let B := {i : α // ¬ a i = true}
  let e := Equiv.piEquivPiSubtypeProd (fun i => a i = true) (fun _ => Bool)
  have he (u : (A → Bool) × (B → Bool)) :
      (∑ i, if a i then sign (e.symm u i) else 0) = ∑ i : A, sign (u.1 i) := by
    rw [← Fintype.sum_subtype_add_sum_subtype (fun i => a i = true)]
    have hpos (i : A) : (if a i then sign (e.symm u i) else 0) = sign (u.1 i) := by
      simp [e, Equiv.piEquivPiSubtypeProd, i.property]
    have hneg (i : B) : (if a i then sign (e.symm u i) else 0) = 0 := by
      simp [e, Equiv.piEquivPiSubtypeProd, i.property]
    simp_rw [hpos, hneg]
    simp only [Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr
    · ext i
      simp
    · intro i hi
      rfl
  have hcard : Fintype.card α = Fintype.card A + Fintype.card B := by
    dsimp [A, B]
    rw [Fintype.card_subtype_compl]
    exact (Nat.add_sub_of_le (Fintype.card_subtype_le _)).symm
  rw [← e.symm.sum_comp]
  simp_rw [he]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool, nsmul_eq_mul]
  rw [hcard, pow_add]
  have factor : (2 : ℝ) ^ (Fintype.card B) * ((1 / 2 : ℝ) ^ (Fintype.card A) * (1 / 2 : ℝ) ^ (Fintype.card B)) =
      (1 / 2 : ℝ) ^ (Fintype.card A) := by
    calc
      _ = (1 / 2 : ℝ) ^ (Fintype.card A) * ((2 : ℝ) ^ (Fintype.card B) * (1 / 2 : ℝ) ^ (Fintype.card B)) := by ring
      _ = _ := by rw [← mul_pow]; norm_num
  calc
    _ = fairTie (α := A) := by
      unfold fairTie
      apply Finset.sum_congr
      · ext v; simp
      intro v hv
      change ((2 ^ (Fintype.card B) : ℕ) : ℝ) *
        (if (∑ i, sign (v i)) = 0 then (1 / 2 : ℝ) ^ (Fintype.card A) * (1 / 2 : ℝ) ^ (Fintype.card B) else 0) =
        if (∑ i, sign (v i)) = 0 then (1 / 2 : ℝ) ^ (Fintype.card A) else 0
      simp only [Nat.cast_pow, Nat.cast_ofNat]
      split_ifs
      · exact factor
      · simp
    _ = _ := fair_tie_formula A

end ActiveFair

namespace Law
open _root_.D5.S3.Arith.FibonacciAtomic
open _root_.D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd (Window first last)
open _root_.D5.S3.Arith.FibonacciAtomic.HeterogeneousTeacherSeparation (extremal)

set_option quotPrecheck false in
local notation "trueClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.1, w.2.2.1, w.2.2.2.1])
set_option quotPrecheck false in
local notation "rivalClass" =>
  (fun w : Record => GarbledPosteriorRootGap.teacher (m := 0)
    ![w.2.1, w.2.2.1, w.2.2.2.1])

/-- The four position laws retain the five actual whole - window symbols. -/
def positionLaw (rho : ℝ) : HeterogeneousTeacherSeparation.Laws 4 :=
  fun i => if i = 0 then biased rho else extremal rho

/-- The exact product expectation of any real observable of the complete record. -/
def expectation (rho a : ℝ) (f : Record → ℝ) : ℝ :=
  ∑ w, recordMass rho a w * f w

/-- The ungarbled class difference of the two actual teachers. -/
def difference (w : Record) : ℝ :=
  ((trueClass w).val : ℝ) - ((rivalClass w).val : ℝ)

/-- Raw score variance in the same complete - record law. -/
def variance (rho a : ℝ) : ℝ :=
  expectation rho a (fun w => (score w : ℝ) ^ 2) -
    (expectation rho a (fun w => (score w : ℝ))) ^ 2

/-- All five symbols satisfy the required lower mass bound at every position. -/
theorem position_law_admissible (rho : ℝ) (hr : 0 < rho) (hr8 : rho ≤ 1 / 8) :
    HeterogeneousTeacherSeparation.Admissible rho (positionLaw rho) := by
  classical
  constructor
  · intro i w
    unfold positionLaw
    split_ifs <;> cases w <;> simp [biased, extremal] <;> linarith
  · intro i
    unfold positionLaw
    split_ifs <;> change (∑ w ∈ ({Window.zero, Window.low, Window.middle, Window.ends, Window.high} : Finset Window), _) = 1
    all_goals simp [biased, extremal]; ring

/-- The pointwise difference preserves the two endpoints of the same third window. -/
theorem difference_formula (w : Record) :
    difference w =
      (HeterogeneousTeacherSeparation.highIndicator w.1 -
        HeterogeneousTeacherSeparation.highIndicator w.2.1) *
      HeterogeneousTeacherSeparation.lowIndicator w.2.2.1 *
      (1 - 2 * HeterogeneousTeacherSeparation.highIndicator w.2.2.1 *
        HeterogeneousTeacherSeparation.lowIndicator w.2.2.2.1) := by
  let t : LegalPriorityTeacher.Roles 4 := ⟨0, 2, 3, by decide, by decide⟩
  let u : LegalPriorityTeacher.Roles 4 := ⟨1, 2, 3, by decide, by decide⟩
  let x : LegalPriorityTeacher.Input 4 := ![w.1, w.2.1, w.2.2.1, w.2.2.2.1]
  have ht := HeterogeneousTeacherSeparation.class_value_formula t x
  have hu := HeterogeneousTeacherSeparation.class_value_formula u x
  simp only [HeterogeneousTeacherSeparation.classValue,
    HeterogeneousTeacherSeparation.firstGate, t, u, x,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Fin.succ_zero_eq_one] at ht hu
  simp only [Fin.succ_one_eq_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail] at ht hu
  unfold difference
  rw [ht, hu]
  ring


/-- Five exact moments hold in the actual joint window - label law. -/
theorem actual_moments (rho a : ℝ) (hr : 0 < rho) (ha : 0 < a) :
    expectation rho a (fun w => difference w ^ 2) = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) ∧
    expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
      (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 ∧
    expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 ∧
    variance rho a = (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) - 9 * a ^ 2 * rho ^ 6 ∧
    0 < expectation rho a (fun w => (score w : ℝ)) := by
  have hd : expectation rho a (fun w => difference w ^ 2) = 2 * rho * (1 - 5 * rho + 12 * rho ^ 2) := by
    unfold expectation
    rw [← one_sum_eq_sum]
    simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, difference, recordMass,
      biased, extremal, channel, GarbledPosteriorRootGap.teacher, first, last]
    ring
  have hn : expectation rho a (fun w => (((trueClass w).val : ℝ) - 1) ^ 2 -
      (((rivalClass w).val : ℝ) - 1) ^ 2) = -2 * rho + 10 * rho ^ 2 := by
    unfold expectation
    rw [← one_sum_eq_sum]
    simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, recordMass,
      biased, extremal, channel, GarbledPosteriorRootGap.teacher, first, last]
    ring
  have hm : expectation rho a (fun w => (score w : ℝ)) = 3 * a * rho ^ 3 := by
    unfold expectation
    rw [← one_sum_eq_sum]
    simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, score, recordMass,
      biased, extremal, channel, GarbledPosteriorRootGap.teacher, first, last]
    ring
  have hs : expectation rho a (fun w => (score w : ℝ) ^ 2) =
      (8 + a) / 12 * (2 * rho * (1 - 5 * rho + 12 * rho ^ 2)) := by
    unfold expectation
    rw [← one_sum_eq_sum]
    simp (config := { maxSteps := 1000000 }) [oneSum, sumWindow, score, recordMass,
      biased, extremal, channel, GarbledPosteriorRootGap.teacher, first, last]
    ring
  refine ⟨hd, hn, hm, ?_, ?_⟩
  · rw [variance, hs, hm]; ring
  · rw [hm]; positivity

end Law

end D5.S3.Arith.FibonacciAtomic.Learning.RawCorrelationMomentIdentities
