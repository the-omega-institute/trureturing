/- GID: D5/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/SymmetricHypercubeWalk/ExchangeableLaws
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Sampling relates fixed Walsh coefficients to radial moments asymptotically. -/

import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.CardEmbedding
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import D5.S3.Quantum.Dynamics.SymmetricHypercubeWalk.WeakLimits
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# Finite sampling with and without replacement

We compare the uniform average over all tuples with the uniform average over
injective tuples, then count collisions by a union bound over pairs of positions.
-/

section

open Finset
open scoped BigOperators

namespace HypercubeSampling

/-- Conditioning a uniform finite average on a nonempty subset changes the mean
of an observable bounded by one by at most twice the discarded fraction. -/
private theorem abs_expect_sub_univ_le {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (hs : s.Nonempty) (f : α → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    |(𝔼 x ∈ s, f x) - (𝔼 x, f x)| ≤
      2 * ((univ \ s).card : ℝ) / Fintype.card α := by
  have : Nonempty α := ⟨hs.choose⟩
  let m : ℝ := 𝔼 x ∈ s, f x
  have hm : |m| ≤ 1 := (Finset.abs_expect_le s f).trans (Finset.expect_le hs (fun x _ ↦ hf x))
  have hcenter : ∑ x ∈ s, (m - f x) = 0 := by
    rw [sum_sub_distrib]
    simp [m, nsmul_eq_mul]
  have hdiff : m - (𝔼 x, f x) = (∑ x ∈ univ \ s, (m - f x)) / Fintype.card α := by
    calc
      _ = (𝔼 x, (m - f x)) := by rw [Finset.expect_sub_distrib, Fintype.expect_const]
      _ = _ := by
        rw [Fintype.expect_eq_sum_div_card, ← sum_sdiff (subset_univ s), hcenter, add_zero]
  change |m - (𝔼 x, f x)| ≤ _
  rw [hdiff, abs_div, abs_of_nonneg (by positivity : 0 ≤ (Fintype.card α : ℝ))]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    |∑ x ∈ univ \ s, (m - f x)| ≤ ∑ x ∈ univ \ s, |m - f x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ (univ : Finset α) \ s, (2 : ℝ) := by
      apply sum_le_sum
      intro x _
      exact abs_le.mpr ⟨by linarith [(abs_le.mp hm).1, (abs_le.mp (hf x)).2],
        by linarith [(abs_le.mp hm).2, (abs_le.mp (hf x)).1]⟩
    _ = _ := by simp [nsmul_eq_mul, mul_comm]

/-- The sample space for ordered sampling without replacement. -/
def injectiveTuples (d k : ℕ) : Finset (Fin k → Fin d) :=
  univ.filter Function.Injective

@[simp]
private theorem mem_injectiveTuples {d k : ℕ} {t : Fin k → Fin d} :
    t ∈ injectiveTuples d k ↔ Function.Injective t := by
  simp [injectiveTuples]

private theorem card_injectiveTuples (d k : ℕ) :
    (injectiveTuples d k).card = d.descFactorial k := by
  let e : {t : Fin k → Fin d // Function.Injective t} ≃ (Fin k ↪ Fin d) :=
    ⟨fun t ↦ ⟨t, t.property⟩, fun t ↦ ⟨t, t.injective⟩, fun _ ↦ rfl, fun _ ↦ rfl⟩
  simpa [Fintype.card_subtype, injectiveTuples, Fintype.card_embedding_eq] using
    Fintype.card_congr e

private theorem card_pairCollision_le (d n : ℕ) {i j : Fin (n + 1)} (hij : i ≠ j) :
    (univ.filter fun t : Fin (n + 1) → Fin d ↦ t i = t j).card ≤ d ^ n := by
  let s : Finset (Fin (n + 1) → Fin d) := univ.filter fun t ↦ t i = t j
  let restrict (t : {t // t ∈ s}) : Fin n → Fin d := fun a ↦ t.val (j.succAbove a)
  have hinj : Function.Injective restrict := by
    intro u v huv
    apply Subtype.ext
    funext a
    have hu : u.val i = u.val j := (mem_filter.mp u.property).2
    have hv : v.val i = v.val j := (mem_filter.mp v.property).2
    have heq (b : Fin (n + 1)) (hb : b ≠ j) : u.val b = v.val b := by
      obtain ⟨r, rfl⟩ := Fin.exists_succAbove_eq hb
      exact congrFun huv r
    by_cases ha : a = j
    · rw [ha, ← hu, ← hv]
      exact heq i hij
    · exact heq a ha
  simpa only [s, Fintype.card_coe, Fintype.card_fun, Fintype.card_fin] using
    Fintype.card_le_of_injective restrict hinj

/-- Counting all colliding tuples by a union bound over unordered position pairs. -/
private theorem card_noninjectiveTuples_le (d n : ℕ) :
    (univ \ injectiveTuples d (n + 1)).card ≤ (n + 1).choose 2 * d ^ n := by
  let positions : Finset (Fin (n + 1)) := univ
  let pairs := (positions ×ˢ positions).filter fun p ↦ p.1 < p.2
  let collide (p : Fin (n + 1) × Fin (n + 1)) : Finset (Fin (n + 1) → Fin d) :=
    univ.filter fun t ↦ t p.1 = t p.2
  have hcover : univ \ injectiveTuples d (n + 1) ⊆ pairs.biUnion collide := by
    intro t ht
    have hbad : ¬ Function.Injective t := by simpa using ht
    unfold Function.Injective at hbad
    push Not at hbad
    obtain ⟨i, j, heq, hne⟩ := hbad
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact mem_biUnion.mpr ⟨(i, j), by simp [pairs, positions, hlt], by simp [collide, heq]⟩
    · exact mem_biUnion.mpr ⟨(j, i), by simp [pairs, positions, hlt], by simp [collide, heq.symm]⟩
  have hcard : pairs.card = (n + 1).choose 2 := by
    simpa [pairs, positions] using (Finset.card_product_filter_lt (s := positions))
  rw [← hcard]
  exact (card_le_card hcover).trans (card_biUnion_le_card_mul pairs collide _ fun p hp ↦
    card_pairCollision_le d n (ne_of_lt (mem_filter.mp hp).2))

private theorem injectiveTuples_nonempty {d k : ℕ} (hk : k ≤ d) :
    (injectiveTuples d k).Nonempty :=
  ⟨(Fin.castLEEmb hk : Fin k ↪ Fin d), mem_injectiveTuples.mpr (Fin.castLEEmb hk).injective⟩

/-- The comparison via the exact fraction of colliding tuples. -/
private theorem abs_expect_injectiveTuples_sub_le_collision {d k : ℕ} (hk : k ≤ d)
    (f : (Fin k → Fin d) → ℝ) (hf : ∀ t, |f t| ≤ 1) :
    |(𝔼 t ∈ injectiveTuples d k, f t) - (𝔼 t, f t)| ≤
      2 * (1 - (d.descFactorial k : ℝ) / (d : ℝ) ^ k) := by
  have hab := abs_expect_sub_univ_le _ (injectiveTuples_nonempty hk) f hf
  have hcard : (Fintype.card (Fin k → Fin d) : ℝ) = (d : ℝ) ^ k := by
    simp
  have hall : 0 < (d : ℝ) ^ k := by
    rw [← hcard]
    have : Nonempty (Fin k → Fin d) := ⟨(injectiveTuples_nonempty hk).choose⟩
    exact_mod_cast Fintype.card_pos
  rw [card_sdiff_of_subset (subset_univ _), card_univ, Nat.cast_sub (card_le_univ _), hcard,
    card_injectiveTuples] at hab
  convert hab using 1
  field_simp

/-- A uniform bound for any observable of the sample with absolute value at most one. -/
private theorem abs_expect_injectiveTuples_sub_le {d k : ℕ} (hk : k ≤ d)
    (f : (Fin k → Fin d) → ℝ) (hf : ∀ t, |f t| ≤ 1) :
    |(𝔼 t ∈ injectiveTuples d k, f t) - (𝔼 t, f t)| ≤
      (k : ℝ) * ((k : ℝ) - 1) / d := by
  cases k with
  | zero =>
    have hs : injectiveTuples d 0 = univ := by
      ext t
      simp only [mem_injectiveTuples, mem_univ, iff_true]
      intro i
      exact Fin.elim0 i
    simp [hs]
  | succ n =>
    have hab := abs_expect_sub_univ_le _ (injectiveTuples_nonempty hk) f hf
    refine hab.trans ?_
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow]
    have hc : ((univ \ injectiveTuples d (n + 1)).card : ℝ) ≤
        ((n + 1).choose 2 : ℝ) * (d : ℝ) ^ n := by
      exact_mod_cast card_noninjectiveTuples_le d n
    have hd' : 0 < (d : ℝ) := by exact_mod_cast (Nat.succ_pos n).trans_le hk
    calc
      _ ≤ 2 * (((n + 1).choose 2 : ℝ) * (d : ℝ) ^ n) / (d : ℝ) ^ (n + 1) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hc (by norm_num)) (by positivity)
      _ = _ := by
        rw [Nat.cast_choose_two, pow_succ]
        field_simp

/-- The product mean for ordered sampling without replacement is within
`k(k-1)/d` of the `k`th power of the population mean. -/
private theorem abs_productMean_sub_pow_le {d k : ℕ} (hk : k ≤ d)
    (z : Fin d → ℝ) (hz : ∀ j, |z j| ≤ 1) :
    |(𝔼 t ∈ injectiveTuples d k, ∏ i, z (t i)) - (𝔼 j, z j) ^ k| ≤
      (k : ℝ) * ((k : ℝ) - 1) / d := by
  rw [Finset.expect_pow, Fintype.piFinset_univ]
  apply abs_expect_injectiveTuples_sub_le hk
  intro t
  rw [Finset.abs_prod]
  exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) (fun i _ ↦ hz (t i))

end HypercubeSampling

end

section

/-!
# Exchangeable hypercube laws

Averaging over injective tuples of coordinates recovers the Walsh coefficient of
an exchangeable law. The finite sampling bound then compares this coefficient
to a shifted moment of the rescaled Hamming weight.
-/

open Finset Filter MeasureTheory
open scoped BigOperators Topology

namespace HypercubeExchangeable

open HypercubeSampling HypercubeWeakLimit

abbrev Configuration (d : ℕ) := Fin d → Bool

/-- A position law preserved by every coordinate permutation. -/
def Exchangeable {d : ℕ} (μ : ProbabilityMeasure (Configuration d)) : Prop :=
  ∀ σ : Equiv.Perm (Fin d), MeasurePreserving
    (fun x : Configuration d ↦ x ∘ σ) (μ : Measure (Configuration d)) μ

/-- The number of nonzero coordinates. -/
def hammingWeight {d : ℕ} (x : Configuration d) : ℕ :=
  (univ.filter fun j ↦ x j = true).card

/-- The normalized Hamming weight, defined also at dimension zero by Lean's
convention for division by zero. -/
noncomputable def normalizedWeight {d : ℕ} (x : Configuration d) : UnitInterval :=
  ⟨(hammingWeight x : ℝ) / d, by
    have hw : (hammingWeight x : ℝ) ≤ d := by
      exact_mod_cast (card_filter_le (univ : Finset (Fin d)) (fun j ↦ x j = true)).trans_eq
        (Fintype.card_fin d)
    exact ⟨by positivity, div_le_one_of_le₀ hw (by positivity)⟩⟩

/-- The law of the normalized Hamming weight. -/
noncomputable def radialLaw {d : ℕ} (μ : ProbabilityMeasure (Configuration d)) :
    ProbabilityMeasure UnitInterval :=
  μ.map normalizedWeight

/-- The sign of a single bit as used in a binary Walsh character. -/
def bitSign (b : Bool) : ℝ := if b then -1 else 1

/-- The sign product along an ordered tuple of coordinates. -/
def tupleSign {d k : ℕ} (x : Configuration d) (t : Fin k → Fin d) : ℝ :=
  ∏ i, bitSign (x (t i))

/-- The Walsh coefficient with support given by an embedding of `k` coordinates. -/
noncomputable def walshCoefficient {d k : ℕ} (μ : ProbabilityMeasure (Configuration d))
    (c : Fin k ↪ Fin d) : ℝ :=
  ∫ x, tupleSign x c ∂(μ : Measure (Configuration d))

private theorem expect_bitSign {d : ℕ} (hd : 0 < d) (x : Configuration d) :
    (𝔼 j, bitSign (x j)) = 1 - 2 * (normalizedWeight x : ℝ) := by
  have hsign (j : Fin d) : bitSign (x j) = 1 - 2 * (if x j = true then (1 : ℝ) else 0) := by
    cases h : x j <;> norm_num [bitSign, h]
  have hsum : (∑ j : Fin d, bitSign (x j)) = (d : ℝ) - 2 * hammingWeight x := by
    simp only [hsign, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, card_univ,
      Fintype.card_fin, mul_one, ← sum_filter, hammingWeight]
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin, hsum]
  change ((d : ℝ) - 2 * hammingWeight x) / d = 1 - 2 * ((hammingWeight x : ℝ) / d)
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  field_simp

/-- The pointwise bound for every sign configuration, uniformly over its Hamming weight. -/
private theorem abs_tupleSignMean_sub_shiftedPower_le {d k : ℕ} (hd : 0 < d) (hk : k ≤ d)
    (x : Configuration d) :
    |(𝔼 t ∈ injectiveTuples d k, tupleSign x t) -
      (1 - 2 * (normalizedWeight x : ℝ)) ^ k| ≤ (k : ℝ) * ((k : ℝ) - 1) / d := by
  rw [← expect_bitSign hd]
  exact abs_productMean_sub_pow_le hk (fun j ↦ bitSign (x j)) fun j ↦ by
    cases h : x j <;> norm_num [bitSign, h]

private theorem integral_tupleSign_eq {d k : ℕ}
    (μ : ProbabilityMeasure (Configuration d)) (hμ : Exchangeable μ)
    (c : Fin k ↪ Fin d) (t : Fin k → Fin d) (ht : Function.Injective t) :
    (∫ x, tupleSign x t ∂(μ : Measure (Configuration d))) = walshCoefficient μ c := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair c t c.injective ht
  have hmap := integral_map (μ := (μ : Measure (Configuration d)))
    (hμ σ).measurable.aemeasurable
    (measurable_of_finite (fun x ↦ tupleSign x c)).aestronglyMeasurable
  rw [(hμ σ).map_eq] at hmap
  rw [walshCoefficient, hmap]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ by simp [tupleSign, hσ])

/-- An exchangeable Walsh coefficient is the integral of the conditional
without-replacement mean given a configuration. -/
private theorem walshCoefficient_eq_integral_expect {d k : ℕ}
    (μ : ProbabilityMeasure (Configuration d)) (hμ : Exchangeable μ) (c : Fin k ↪ Fin d) :
    walshCoefficient μ c =
      ∫ x, (𝔼 t ∈ injectiveTuples d k, tupleSign x t) ∂(μ : Measure (Configuration d)) := by
  let s := injectiveTuples d k
  have hs : s.Nonempty := ⟨c, mem_injectiveTuples.mpr c.injective⟩
  simp only [Finset.expect_eq_sum_div_card, integral_div]
  rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  rw [sum_congr rfl (fun t ht ↦ integral_tupleSign_eq μ hμ c t (mem_injectiveTuples.mp ht))]
  have hs' : ((injectiveTuples d k).card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  simp [nsmul_eq_mul, hs']

private theorem shiftedMoment_radialLaw_eq {d : ℕ} (hd : 0 < d)
    (μ : ProbabilityMeasure (Configuration d)) (k : ℕ) :
    shiftedMoment (radialLaw μ) k =
      ∫ x, (𝔼 j, bitSign (x j)) ^ k ∂(μ : Measure (Configuration d)) := by
  change (∫ x, shiftedCoordinate x ^ k ∂(μ.map normalizedWeight).toMeasure) = _
  have hstrong : StronglyMeasurable (fun x : UnitInterval ↦ shiftedCoordinate x ^ k) :=
    (shiftedCoordinate.continuous.pow k).stronglyMeasurable
  rw [ProbabilityMeasure.toMeasure_map, integral_map
    (measurable_of_finite normalizedWeight).aemeasurable hstrong.aestronglyMeasurable]
  exact integral_congr_ae (Eventually.of_forall fun x ↦
    congrArg (fun r : ℝ ↦ r ^ k) (expect_bitSign hd x).symm)

/-- The finite sampling estimate after averaging over an exchangeable position law. -/
theorem abs_walshCoefficient_sub_shiftedMoment_le {d k : ℕ}
    (μ : ProbabilityMeasure (Configuration d)) (hμ : Exchangeable μ) (c : Fin k ↪ Fin d) :
    |walshCoefficient μ c - shiftedMoment (radialLaw μ) k| ≤
      (k : ℝ) * ((k : ℝ) - 1) / d := by
  have hk : k ≤ d := by simpa using Fintype.card_le_of_embedding c
  rcases d.eq_zero_or_pos with rfl | hd
  · have : k = 0 := Nat.eq_zero_of_le_zero hk
    subst k
    simp [walshCoefficient, tupleSign, shiftedMoment]
  rw [walshCoefficient_eq_integral_expect μ hμ c, shiftedMoment_radialLaw_eq hd,
    ← integral_sub Integrable.of_finite Integrable.of_finite]
  rw [← Real.norm_eq_abs]
  have hbound (x : Configuration d) :
      ‖(𝔼 t ∈ injectiveTuples d k, tupleSign x t) - (𝔼 j, bitSign (x j)) ^ k‖ ≤
        (k : ℝ) * ((k : ℝ) - 1) / d := by
    rw [Real.norm_eq_abs, expect_bitSign hd]
    exact abs_tupleSignMean_sub_shiftedPower_le hd hk x
  simpa using norm_integral_le_of_norm_le_const (μ := (μ : Measure (Configuration d)))
    (Eventually.of_forall hbound)

/-- The error when the shifted-moment gap is used in place of the Walsh gap
for two exchangeable laws. -/
private theorem abs_shiftedMomentGap_sub_walshGap_le {d k : ℕ}
    (μ ν : ProbabilityMeasure (Configuration d)) (hμ : Exchangeable μ) (hν : Exchangeable ν)
    (c : Fin k ↪ Fin d) :
    |(shiftedMoment (radialLaw μ) k - shiftedMoment (radialLaw ν) k) -
      (walshCoefficient μ c - walshCoefficient ν c)| ≤
      2 * (k : ℝ) * ((k : ℝ) - 1) / d := by
  have h₁ := abs_walshCoefficient_sub_shiftedMoment_le μ hμ c
  have h₂ := abs_walshCoefficient_sub_shiftedMoment_le ν hν c
  rw [abs_sub_comm] at h₁ h₂
  have hrewrite :
      (shiftedMoment (radialLaw μ) k - shiftedMoment (radialLaw ν) k) -
        (walshCoefficient μ c - walshCoefficient ν c) =
      (shiftedMoment (radialLaw μ) k - walshCoefficient μ c) -
        (shiftedMoment (radialLaw ν) k - walshCoefficient ν c) := by ring
  rw [hrewrite, ← Real.norm_eq_abs]
  refine (norm_sub_le _ _).trans ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  exact (add_le_add h₁ h₂).trans_eq (by ring)

section DimensionLimit

variable (μ ν : (d : ℕ) → ProbabilityMeasure (Configuration d))
  (hμ : ∀ d, Exchangeable (μ d)) (hν : ∀ d, Exchangeable (ν d))
  (G : ℕ → ℕ → ℝ)

include hμ hν


/-- The two gap sequences have the same vanishing criterion if the proposed
finite gap agrees eventually with a Walsh gap at every fixed positive order. -/
private theorem tendsto_shiftedMomentGap_iff_tendsto_finiteGap
    (hG : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      G d k = walshCoefficient (μ d) c - walshCoefficient (ν d) c) :
    (∀ k : ℕ, 0 < k → Tendsto
      (fun d ↦ shiftedMoment (radialLaw (μ d)) k - shiftedMoment (radialLaw (ν d)) k)
      atTop (𝓝 0)) ↔
    (∀ k : ℕ, 0 < k → Tendsto (G · k) atTop (𝓝 0)) := by
  let M (d k : ℕ) := shiftedMoment (radialLaw (μ d)) k - shiftedMoment (radialLaw (ν d)) k
  change (∀ k : ℕ, 0 < k → Tendsto (M · k) atTop (𝓝 0)) ↔ _
  have herr (k : ℕ) (hk : 0 < k) : Tendsto (fun d ↦ M d k - G d k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat (2 * (k : ℝ) * ((k : ℝ) - 1)))
    filter_upwards [hG k hk] with d hvalid
    obtain ⟨c, hc⟩ := hvalid
    rw [Real.norm_eq_abs, hc]
    exact abs_shiftedMomentGap_sub_walshGap_le (μ d) (ν d) (hμ d) (hν d) c
  constructor
  · intro h k hk
    simpa using (h k hk).sub (herr k hk)
  · intro h k hk
    simpa using (herr k hk).add (h k hk)

/-- Vanishing of each fixed positive-weight finite gap is equivalent to
asymptotic agreement of the radial laws on every continuous test. -/
theorem tendsto_integral_sub_iff_tendsto_finiteGap
    (hG : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      G d k = walshCoefficient (μ d) c - walshCoefficient (ν d) c) :
    (∀ f : C(UnitInterval, ℝ), Tendsto (fun d ↦
      (∫ x, f x ∂(radialLaw (μ d) : Measure UnitInterval)) -
        ∫ x, f x ∂(radialLaw (ν d) : Measure UnitInterval)) atTop (𝓝 0)) ↔
    (∀ k : ℕ, 0 < k → Tendsto (G · k) atTop (𝓝 0)) :=
  (tendsto_integral_sub_iff_shiftedMoments atTop
    ((fun d ↦ radialLaw (μ d))) ((fun d ↦ radialLaw (ν d)))).trans
    (tendsto_shiftedMomentGap_iff_tendsto_finiteGap μ ν hμ hν G hG)

/-- If either family of radial laws converges weakly to `π`, then both converge
weakly to `π` exactly when each fixed positive-weight finite gap vanishes. -/
theorem common_weakLimit_iff_tendsto_finiteGap
    (hG : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      G d k = walshCoefficient (μ d) c - walshCoefficient (ν d) c)
    (π : ProbabilityMeasure UnitInterval)
    (h : Tendsto ((fun d ↦ radialLaw (μ d))) atTop (𝓝 π) ∨
      Tendsto ((fun d ↦ radialLaw (ν d))) atTop (𝓝 π)) :
    (Tendsto ((fun d ↦ radialLaw (μ d))) atTop (𝓝 π) ∧
      Tendsto ((fun d ↦ radialLaw (ν d))) atTop (𝓝 π)) ↔
    (∀ k : ℕ, 0 < k → Tendsto (G · k) atTop (𝓝 0)) :=
  (common_weakLimit_iff_shiftedMoments atTop
    ((fun d ↦ radialLaw (μ d))) ((fun d ↦ radialLaw (ν d))) π h).trans
    (tendsto_shiftedMomentGap_iff_tendsto_finiteGap μ ν hμ hν G hG)

end DimensionLimit

/-- The radial laws of one exchangeable family converge weakly exactly when
each fixed positive-order Walsh coefficient converges. The values outside the
eventual range of admissible dimensions are arbitrary. -/
private theorem exists_radialWeakLimit_iff_finiteCoefficients
    (μ : (d : ℕ) → ProbabilityMeasure (Configuration d)) (hμ : ∀ d, Exchangeable (μ d))
    (B : ℕ → ℕ → ℝ)
    (hB : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      B d k = walshCoefficient (μ d) c) :
    (∃ π : ProbabilityMeasure UnitInterval, Tendsto (fun d ↦ radialLaw (μ d)) atTop (𝓝 π)) ↔
    (∀ k : ℕ, 0 < k → ∃ m : ℝ, Tendsto (B · k) atTop (𝓝 m)) := by
  rw [exists_weakLimit_iff_shiftedMoments_converge]
  have herr (k : ℕ) (hk : 0 < k) :
      Tendsto (fun d ↦ shiftedMoment (radialLaw (μ d)) k - B d k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ (tendsto_const_div_atTop_nhds_zero_nat ((k : ℝ) * ((k : ℝ) - 1)))
    filter_upwards [hB k hk] with d hvalid
    obtain ⟨c, hc⟩ := hvalid
    rw [Real.norm_eq_abs, hc, abs_sub_comm]
    exact abs_walshCoefficient_sub_shiftedMoment_le (μ d) (hμ d) c
  constructor
  · intro h k hk
    obtain ⟨m, hm⟩ := h k hk
    exact ⟨m, by simpa using hm.sub (herr k hk)⟩
  · intro h k hk
    obtain ⟨m, hm⟩ := h k hk
    exact ⟨m, by simpa using (herr k hk).add hm⟩

/-- The existence-inclusive criterion in terms of finite coefficients. The
coefficient `B` comes from the first family, and `G` is the gap between the two. -/
theorem exists_common_weakLimit_iff_finiteCoefficients
    (μ ν : (d : ℕ) → ProbabilityMeasure (Configuration d))
    (hμ : ∀ d, Exchangeable (μ d)) (hν : ∀ d, Exchangeable (ν d))
    (B G : ℕ → ℕ → ℝ)
    (hB : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      B d k = walshCoefficient (μ d) c)
    (hG : ∀ k : ℕ, 0 < k → ∀ᶠ d in atTop, ∃ c : Fin k ↪ Fin d,
      G d k = walshCoefficient (μ d) c - walshCoefficient (ν d) c) :
    (∃ π : ProbabilityMeasure UnitInterval,
      Tendsto (fun d ↦ radialLaw (μ d)) atTop (𝓝 π) ∧
      Tendsto (fun d ↦ radialLaw (ν d)) atTop (𝓝 π)) ↔
    ((∀ k : ℕ, 0 < k → Tendsto (G · k) atTop (𝓝 0)) ∧
      (∀ k : ℕ, 0 < k → ∃ m : ℝ, Tendsto (B · k) atTop (𝓝 m))) := by
  have hfirst := exists_radialWeakLimit_iff_finiteCoefficients μ hμ B hB
  constructor
  · rintro ⟨π, hμlim, hνlim⟩
    exact ⟨(common_weakLimit_iff_tendsto_finiteGap μ ν hμ hν G hG π (.inl hμlim)).mp
      ⟨hμlim, hνlim⟩, hfirst.mp ⟨π, hμlim⟩⟩
  · rintro ⟨hgap, hcoeff⟩
    obtain ⟨π, hμlim⟩ := hfirst.mpr hcoeff
    exact ⟨π, (common_weakLimit_iff_tendsto_finiteGap μ ν hμ hν G hG π (.inl hμlim)).mpr hgap⟩

end HypercubeExchangeable

end
