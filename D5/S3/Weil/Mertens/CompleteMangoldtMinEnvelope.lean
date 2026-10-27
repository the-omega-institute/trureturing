/- GID: D5/S3/Weil/Mertens/CompleteMangoldtMinEnvelope
   generality: G
   mirror-B: D5/B/S3/Weil/Mertens/CompleteMangoldtMinEnvelope
   mirror-E: none(waiver:infinite-arithmetic-envelope)
   anchors: []
   utility: none
   digest: Full Mangoldt min envelope with an explicit four-fifths bound. -/

import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-!
   This module proves the actual complete Mangoldt estimate rather than assuming
   a head or tail bound. The two Abel boundary terms at R=L^(2/5)
   cancel exactly. No prime or prime-power coefficient is discarded.
   Reuse: the same Abel/psi normalization as CompleteChebyshevTailIdentity;
   Mathlib owns Abel summation and the explicit linear Chebyshev bound.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope

open Real Set MeasureTheory Filter
open scoped Topology BigOperators

private def cPsi : ℝ := Real.log 4 + 4

private theorem cPsi_nonneg : 0 ≤ cPsi := by
  have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  dsimp only [cPsi]
  linarith

/-- The literal coefficient, including all prime powers and their actual weights. -/
def mangoldtMinTerm (L : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / Real.sqrt n *
    min L⁻¹ ((n : ℝ) ^ (-5 / 2 : ℝ))

private theorem term_nonneg {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 ≤ mangoldtMinTerm L n := by
  unfold mangoldtMinTerm
  exact mul_nonneg
    (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (le_min (inv_nonneg.mpr hL.le) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

private theorem term_le_head {L : ℝ} (n : ℕ) :
    mangoldtMinTerm L n ≤
      L⁻¹ * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-1 / 2 : ℝ)) := by
  unfold mangoldtMinTerm
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n * L⁻¹ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    _ = _ := by
      rw [Real.sqrt_eq_rpow,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg (Nat.cast_nonneg n)]
      ring

private theorem term_le_tail {L : ℝ} (n : ℕ) :
    mangoldtMinTerm L n ≤
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-3 : ℝ) := by
  by_cases hn : n = 0
  · subst n
    simp [mangoldtMinTerm]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold mangoldtMinTerm
  calc
    _ ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        (n : ℝ) ^ (-5 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _)
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    _ = ArithmeticFunction.vonMangoldt n *
        ((n : ℝ) ^ (-1 / 2 : ℝ) * (n : ℝ) ^ (-5 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow,
        show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hn0.le]
      ring
    _ = _ := by
      rw [← Real.rpow_add hn0]
      norm_num

private theorem mul_rpow_shift {x : ℝ} (hx : 0 < x) (p : ℝ) :
    x * x ^ p = x ^ (p + 1) := by
  calc
    _ = x ^ (1 : ℝ) * x ^ p := by rw [Real.rpow_one]
    _ = x ^ ((1 : ℝ) + p) := (Real.rpow_add hx _ _).symm
    _ = _ := by congr 1; ring

private theorem rpow_continuousOn {a b : ℝ} (ha : 0 < a) (p : ℝ) :
    ContinuousOn (fun x : ℝ => x ^ p) (Icc a b) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p
    (Or.inl (ne_of_gt (ha.trans_le hx.1)))).continuousWithinAt

private theorem psi_rpow_integral_le {a b : ℝ} (ha : 0 < a) (p : ℝ) :
    (∫ x in Ioc a b, Chebyshev.psi x * x ^ p) ≤
      cPsi * ∫ x in Ioc a b, x ^ (p + 1) := by
  have hi : IntegrableOn (fun x : ℝ => cPsi * x ^ (p + 1)) (Ioc a b) :=
    by
      have hcc : IntegrableOn (fun x : ℝ => cPsi * x ^ (p + 1)) (Icc a b) :=
        ((rpow_continuousOn ha (p + 1)).integrableOn_Icc).const_mul cPsi
      exact hcc.mono_set Ioc_subset_Icc_self
  have hp (x : ℝ) (hx : x ∈ Ioc a b) :
      Chebyshev.psi x * x ^ p ≤ cPsi * x ^ (p + 1) := by
    have hx0 : 0 < x := ha.trans hx.1
    calc
      _ ≤ (cPsi*x) * x ^ p := mul_le_mul_of_nonneg_right
        (Chebyshev.psi_le_const_mul_self hx0.le) (Real.rpow_nonneg hx0.le _)
      _ = _ := by rw [mul_assoc, mul_rpow_shift hx0]
  have hm : AEStronglyMeasurable
      (fun x : ℝ => Chebyshev.psi x * x ^ p) (volume.restrict (Ioc a b)) :=
    (Chebyshev.psi_mono.measurable.mul (by fun_prop)).aestronglyMeasurable
  have hpi : IntegrableOn (fun x : ℝ => Chebyshev.psi x * x ^ p) (Ioc a b) := by
    refine hi.mono' hm ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (Chebyshev.psi_nonneg x) (Real.rpow_nonneg (le_of_lt (ha.trans hx.1)) _))]
    exact hp x hx
  calc
    _ ≤ ∫ x in Ioc a b, cPsi * x ^ (p + 1) := by
      apply integral_mono_ae hpi hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      exact hp x hx
    _ = _ := integral_const_mul _ _

private theorem weighted_abel_prefix {b : ℝ} (hb : 1 ≤ b) (p : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ p) =
      Chebyshev.psi b * b ^ p -
        p * ∫ x in Ioc (1 : ℝ) b, Chebyshev.psi x * x ^ (p - 1) := by
  have hd (x : ℝ) (hx : x ∈ Icc (1 : ℝ) b) :
      HasDerivAt (fun y : ℝ => y ^ p) (p*x^(p-1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (zero_lt_one.trans_le hx.1)))
  have hci : ContinuousOn (fun x : ℝ => p*x^(p-1)) (Icc (1 : ℝ) b) :=
    continuousOn_const.mul (rpow_continuousOn one_pos (p-1))
  have hdi : IntegrableOn (deriv fun y : ℝ => y ^ p) (Icc (1 : ℝ) b) := by
    refine hci.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro x hx
    exact (hd x hx).deriv.symm
  have h := sum_mul_eq_sub_integral_mul₀
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) (by simp) b
    (f := fun x : ℝ => x ^ p) (fun x hx => (hd x hx).differentiableAt) hdi
  have hs : (∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
      (n : ℝ)^p * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Icc 0 ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt n * (n : ℝ)^p := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi : (∫ x in Ioc (1 : ℝ) b,
      deriv (fun y : ℝ => y ^ p) x *
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) =
      p * ∫ x in Ioc (1 : ℝ) b, Chebyshev.psi x * x ^ (p-1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(hd x ⟨hx.1.le, hx.2⟩).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hs, ← Chebyshev.psi_eq_sum_Icc, hi] at h
  simpa only [mul_comm (b ^ p)] using h

private theorem weighted_abel_tail {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (p : ℝ) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ p) =
      Chebyshev.psi b * b ^ p - Chebyshev.psi a * a ^ p -
        p * ∫ x in Ioc a b, Chebyshev.psi x * x ^ (p-1) := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hd (x : ℝ) (hx : x ∈ Icc a b) :
      HasDerivAt (fun y : ℝ => y ^ p) (p*x^(p-1)) x :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt (ha0.trans_le hx.1)))
  have hci : ContinuousOn (fun x : ℝ => p*x^(p-1)) (Icc a b) :=
    continuousOn_const.mul (rpow_continuousOn ha0 (p-1))
  have hdi : IntegrableOn (deriv fun y : ℝ => y ^ p) (Icc a b) := by
    refine hci.integrableOn_Icc.congr_fun ?_ measurableSet_Icc
    intro x hx
    exact (hd x hx).deriv.symm
  have h := sum_mul_eq_sub_sub_integral_mul
    (fun n : ℕ => ArithmeticFunction.vonMangoldt n) ha0.le hab
    (f := fun x : ℝ => x ^ p) (fun x hx => (hd x hx).differentiableAt) hdi
  have hs : (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
      (n : ℝ)^p * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ArithmeticFunction.vonMangoldt n * (n : ℝ)^p := by
    apply Finset.sum_congr rfl
    intro n _
    ring
  have hi : (∫ x in Ioc a b,
      deriv (fun y : ℝ => y ^ p) x *
        ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n) =
      p * ∫ x in Ioc a b, Chebyshev.psi x * x ^ (p-1) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    dsimp only
    rw [(hd x ⟨hx.1.le, hx.2⟩).deriv, ← Chebyshev.psi_eq_sum_Icc]
    ring
  rw [hs, ← Chebyshev.psi_eq_sum_Icc, ← Chebyshev.psi_eq_sum_Icc, hi] at h
  simpa only [mul_comm (b ^ p), mul_comm (a ^ p)] using h

private theorem half_integral {b : ℝ} (hb : 1 ≤ b) :
    (∫ x in Ioc (1 : ℝ) b, x ^ (-1/2 : ℝ)) = 2 * (b^(1/2 : ℝ)-1) := by
  rw [← intervalIntegral.integral_of_le hb,
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -1/2))]
  norm_num; ring

private theorem cube_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫ x in Ioc a b, x ^ (-3 : ℝ)) =
      (a^(-2 : ℝ) - b^(-2 : ℝ))/2 := by
  have hz : (0 : ℝ) ∉ Set.uIcc a b := by
    rw [Set.uIcc_of_le hab]
    intro h
    linarith [h.1]
  rw [← intervalIntegral.integral_of_le hab,
    integral_rpow (Or.inr ⟨by norm_num, hz⟩)]
  norm_num; ring

private theorem head_abel_bound {R : ℝ} (hR : 1 ≤ R) :
    (∑ n ∈ Finset.Icc 0 ⌊R⌋₊,
      ArithmeticFunction.vonMangoldt n * (n : ℝ)^(-1/2 : ℝ)) ≤
      Chebyshev.psi R * R^(-1/2 : ℝ) + cPsi * (R^(1/2 : ℝ)-1) := by
  have hi := psi_rpow_integral_le (b := R) one_pos (-3/2)
  norm_num only at hi
  have hhalf := half_integral hR
  norm_num only at hhalf
  rw [hhalf] at hi
  rw [weighted_abel_prefix hR (-1/2)]
  norm_num only
  linarith

private theorem tail_abel_bound {R B : ℝ} (hR : 1 ≤ R) (hRB : R ≤ B) :
    (∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊B⌋₊,
      ArithmeticFunction.vonMangoldt n * (n : ℝ)^(-3 : ℝ)) ≤
      -Chebyshev.psi R * R^(-3 : ℝ) +
        (3/2 : ℝ)*cPsi*R^(-2 : ℝ) - (1/2 : ℝ)*cPsi*B^(-2 : ℝ) := by
  have hR0 := zero_lt_one.trans_le hR
  have hB0 := hR0.trans_le hRB
  have hi := psi_rpow_integral_le (b := B) hR0 (-4)
  norm_num only at hi
  rw [cube_integral hR0 hRB] at hi
  have hp : Chebyshev.psi B * B^(-3 : ℝ) ≤ cPsi*B^(-2 : ℝ) := by
    calc
      _ ≤ (cPsi*B)*B^(-3 : ℝ) := mul_le_mul_of_nonneg_right
        (Chebyshev.psi_le_const_mul_self hB0.le) (Real.rpow_nonneg hB0.le _)
      _ = _ := by rw [mul_assoc, mul_rpow_shift hB0]; norm_num
  rw [weighted_abel_tail hR hRB (-3)]
  norm_num only
  linarith

private theorem finite_sum_partition {L R B : ℝ} (hRB : R ≤ B) :
    (∑ n ∈ Finset.Icc 0 ⌊B⌋₊, mangoldtMinTerm L n) ≤
      L⁻¹ * (∑ n ∈ Finset.Icc 0 ⌊R⌋₊,
        ArithmeticFunction.vonMangoldt n * (n : ℝ)^(-1/2 : ℝ)) +
      ∑ n ∈ Finset.Ioc ⌊R⌋₊ ⌊B⌋₊,
        ArithmeticFunction.vonMangoldt n * (n : ℝ)^(-3 : ℝ) := by
  have hfloor := Nat.floor_le_floor hRB
  have hpart : Finset.Icc 0 ⌊B⌋₊ =
      Finset.Icc 0 ⌊R⌋₊ ∪ Finset.Ioc ⌊R⌋₊ ⌊B⌋₊ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdis : Disjoint (Finset.Icc 0 ⌊R⌋₊) (Finset.Ioc ⌊R⌋₊ ⌊B⌋₊) := by
    apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [Finset.mem_Icc, Finset.mem_Ioc] at hn hm
    omega
  rw [hpart, Finset.sum_union hdis, Finset.mul_sum]
  exact add_le_add
    (Finset.sum_le_sum fun n _ => term_le_head n)
    (Finset.sum_le_sum fun n _ => term_le_tail n)

private theorem cutoff_power_identities {L : ℝ} (hL : 0 < L) :
    let R := L ^ (2 / 5 : ℝ)
    L⁻¹ * R^(-1/2 : ℝ) = R^(-3 : ℝ) ∧
      L⁻¹ * R^(1/2 : ℝ) = L^(-4/5 : ℝ) ∧
      R^(-2 : ℝ) = L^(-4/5 : ℝ) := by
  dsimp only
  have hp (p : ℝ) : (L ^ (2 / 5 : ℝ))^p = L^((2/5 : ℝ)*p) :=
    (Real.rpow_mul hL.le _ _).symm
  have hinv : L⁻¹ = L^(-1 : ℝ) := (Real.rpow_neg_one L).symm
  constructor
  · rw [hp, hp, hinv, ← Real.rpow_add hL]
    congr 1
    ring
  constructor
  · rw [hp, hinv, ← Real.rpow_add hL]
    congr 1
    ring
  · rw [hp]
    congr 1
    ring

private theorem finite_min_bound {L B : ℝ} (hL : 1 ≤ L)
    (hB : L ^ (2 / 5 : ℝ) ≤ B) :
    (∑ n ∈ Finset.Icc 0 ⌊B⌋₊, mangoldtMinTerm L n) ≤
      (5/2 : ℝ)*cPsi*L^(-4/5 : ℝ) := by
  let R := L ^ (2 / 5 : ℝ)
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hR : 1 ≤ R := Real.one_le_rpow hL (by norm_num)
  obtain ⟨hcancel, hhead, htail⟩ := cutoff_power_identities hL0
  have hh := head_abel_bound hR
  have ht := tail_abel_bound hR hB
  have hp := finite_sum_partition (L := L) hB
  have hs := hp.trans (add_le_add
    (mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hL0.le)) ht)
  have hcancel' : L⁻¹ * (Chebyshev.psi R * R^(-1/2 : ℝ)) =
      Chebyshev.psi R * R^(-3 : ℝ) := by
    calc
      _ = Chebyshev.psi R * (L⁻¹*R^(-1/2 : ℝ)) := by ring
      _ = _ := by rw [hcancel]
  have hhead' : L⁻¹*(cPsi*(R^(1/2 : ℝ)-1)) =
      cPsi*L^(-4/5 : ℝ) - cPsi*L⁻¹ := by
    calc
      _ = cPsi*(L⁻¹*R^(1/2 : ℝ)) - cPsi*L⁻¹ := by ring
      _ = _ := by rw [hhead]
  have htail' : (3/2 : ℝ)*cPsi*R^(-2 : ℝ) =
      (3/2 : ℝ)*cPsi*L^(-4/5 : ℝ) := by rw [htail]
  have hc1 : 0 ≤ cPsi*L⁻¹ := mul_nonneg cPsi_nonneg (inv_nonneg.mpr hL0.le)
  have hc2 : 0 ≤ (1/2 : ℝ)*cPsi*B^(-2 : ℝ) := by
    exact mul_nonneg (mul_nonneg (by norm_num) cPsi_nonneg)
      (Real.rpow_nonneg ((zero_lt_one.trans_le hR).le.trans hB) _)
  rw [mul_add, hcancel', hhead', htail'] at hs
  linarith

private theorem all_range_bounds {L : ℝ} (hL : 1 ≤ L) (m : ℕ) :
    (∑ n ∈ Finset.range m, mangoldtMinTerm L n) ≤
      (5/2 : ℝ)*cPsi*L^(-4/5 : ℝ) := by
  let B := max (L ^ (2 / 5 : ℝ)) (m : ℝ)
  have hsub : Finset.range m ⊆ Finset.Icc 0 ⌊B⌋₊ := by
    intro n hn
    apply Finset.mem_Icc.mpr
    refine ⟨Nat.zero_le n, Nat.le_floor ?_⟩
    exact (Nat.cast_le.mpr (Nat.le_of_lt (Finset.mem_range.mp hn))).trans (le_max_right _ _)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 0 ⌊B⌋₊, mangoldtMinTerm L n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => term_nonneg (zero_lt_one.trans_le hL) n)
    _ ≤ _ := finite_min_bound hL (le_max_left _ _)

/-- The complete actual prime-power envelope has a uniform four-fifths
rate for every L>=1. The Chebyshev and Abel estimates are proved on the
live path; the result assumes no head/tail estimate and no RH premise. -/
theorem complete_mangoldt_min_envelope {L : ℝ} (hL : 1 ≤ L) :
    Summable (mangoldtMinTerm L) ∧
      (∑' n : ℕ, mangoldtMinTerm L n) ≤
        (5/2 : ℝ) * (Real.log 4 + 4) * L^(-4/5 : ℝ) := by
  have hn := term_nonneg (zero_lt_one.trans_le hL)
  have hb := all_range_bounds hL
  exact ⟨summable_of_sum_range_le hn hb, Real.tsum_le_of_sum_range_le hn hb⟩

#print axioms complete_mangoldt_min_envelope

end D5.S3.Weil.Mertens.CompleteMangoldtMinEnvelope
