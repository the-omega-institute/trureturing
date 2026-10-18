/-
SOURCE_ONLY_UNCOMPILED. Full proof attempts, with no elaboration/kernel claim.
Install at D5/S3/Weil/ZetaBridge/PrimeSymbolResonance.lean only in a later,
authorized integration. Requires the proposed T2 and owner visibility patches.
The imported T2 source is itself UNCOMPILED. No physical chain is imported.
-/
import D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Divisors
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Weil.ZetaBridge.PrimeSymbolResonance

open scoped BigOperators ComplexConjugate
open D5.S3.Weil.ZetaBridge.PrimeSymbolMeanSquare
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- ORDERED resonant pairs, including p=q when p^2=c. -/
def resonantMass (c : ℕ) : ℝ :=
  ∑ p ∈ primeIndices c, ∑ q ∈ primeIndices c,
    if p * q = c then primeWeight p * primeWeight q else 0

/-- The factor 2 is per ordered pair, exactly as in T2.orderedCross. -/
def sumCross (c : ℕ) : ℝ :=
  ∑ p ∈ primeIndices c, ∑ q ∈ primeIndices c,
    if p * q = c then 0 else
      2 * |primeWeight p * primeWeight q| / ‖1 - primePhase c p * primePhase c q‖

def mean (c : ℕ) : ℝ := (primeSquareMass c - resonantMass c) / 2

def offset (c : ℕ) : ℝ := (primeCross c + sumCross c) / 2

def tailBudget (c N : ℕ) : ℝ :=
  mean c / (N : ℝ) + offset c / ((N : ℝ) + 1) ^ 2

/-- The difference classification uses T2's actual-log noncollision proof. -/
theorem difference_resonance {c p q : ℕ} (hc : 2 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) :
    primePhase c p * conj (primePhase c q) = 1 ↔ p = q := by
  constructor
  · intro h
    by_contra hpq
    exact primePhase_noncollision hc hp hq hpq h
  · rintro rfl
    rw [Complex.mul_conj', primePhase_norm]
    norm_num

private theorem phase_product (c p q : ℕ) :
    primePhase c p * primePhase c q =
      circleMap 0 1 (2 * Real.pi * (theta c p + theta c q)) := by
  simpa only [primePhase, one_mul, mul_add] using
    circleMap_zero_mul 1 1 (2 * Real.pi * theta c p) (2 * Real.pi * theta c q)

/-- The sum angle lies in (0,4pi), so its only circle identity is 2pi.
No spacing, irrationality, or equidistribution premise occurs. -/
theorem sum_resonance {c p q : ℕ} (hc : 2 ≤ c)
    (hp : p ∈ primeIndices c) (hq : q ∈ primeIndices c) :
    primePhase c p * primePhase c q = 1 ↔ p * q = c := by
  have hL := logLength_pos hc
  obtain ⟨hp0, hp1⟩ := phase_geometry hc hp
  obtain ⟨hq0, hq1⟩ := phase_geometry hc hq
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by
    have := (Finset.mem_Ico.mp hp).1; omega)
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by
    have := (Finset.mem_Ico.mp hq).1; omega)
  have hcR : (0 : ℝ) < c := by exact_mod_cast (show 0 < c by omega)
  have hperiod : circleMap (0 : ℂ) 1 (2 * Real.pi) = 1 := by
    simpa [circleMap] using (periodic_circleMap (0 : ℂ) 1) 0
  have hperiodpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have hlo : 0 < 2 * Real.pi * (theta c p + theta c q) :=
    mul_pos hperiodpos (add_pos hp0 hq0)
  have hhi : 2 * Real.pi * (theta c p + theta c q) < (2 * Real.pi) * 2 :=
    mul_lt_mul_of_pos_left (by linarith : theta c p + theta c q < 2) hperiodpos
  have hdist :
      |2 * Real.pi * (theta c p + theta c q) - 2 * Real.pi| < 2 * Real.pi := by
    exact abs_lt.mpr ⟨by linarith, by linarith⟩
  rw [phase_product]
  constructor
  · intro h
    have hang := eq_of_circleMap_eq (by norm_num : (1 : ℝ) ≠ 0) hdist
      (h.trans hperiod.symm)
    have ht : theta c p + theta c q = 1 := by
      apply mul_left_cancel₀ (ne_of_gt hperiodpos)
      simpa only [mul_one] using hang
    have hlogs : Real.log (p : ℝ) + Real.log (q : ℝ) = Real.log (c : ℝ) := by
      dsimp [theta, logLength] at ht hL
      field_simp [hL.ne'] at ht
      linarith
    have heq : (p : ℝ) * (q : ℝ) = c :=
      Real.log_injOn_pos (mul_pos hpR hqR) hcR
        ((Real.log_mul hpR.ne' hqR.ne').trans hlogs)
    exact_mod_cast heq
  · intro hpq
    have hprod : (p : ℝ) * (q : ℝ) = c := by exact_mod_cast hpq
    have hlogs : Real.log (p : ℝ) + Real.log (q : ℝ) = logLength c := by
      rw [← Real.log_mul hpR.ne' hqR.ne', hprod]
      rfl
    have ht : theta c p + theta c q = 1 := by
      dsimp [theta]
      rw [← add_div, hlogs, div_self hL.ne']
    rw [ht, mul_one, hperiod]

/-- A single centered geometric channel. The sole geometric bound is T2's. -/
private theorem centered_geometric {z : ℂ} (hz : ‖z‖ = 1)
    (b : ℝ) (M : ℤ) (K : ℕ) :
    |(∑ j ∈ Finset.range K, ((b : ℂ) * z ^ (M + (j : ℤ))).re) -
      (K : ℝ) * (if z = 1 then b else 0)| ≤
        if z = 1 then 0 else 2 * |b| / ‖1 - z‖ := by
  classical
  by_cases hz1 : z = 1
  · simp [hz1, nsmul_eq_mul]
  · rw [if_neg hz1, if_neg hz1, mul_zero, sub_zero]
    have hg := geometric_block_norm hz hz1 M K
    calc
      _ = |((b : ℂ) * ∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))).re| := by
        rw [Finset.mul_sum]
        exact congrArg abs (map_sum Complex.reAddGroupHom _ _).symm
      _ ≤ ‖(b : ℂ) * ∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))‖ :=
        Complex.abs_re_le_norm _
      _ = |b| * ‖∑ j ∈ Finset.range K, z ^ (M + (j : ℤ))‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      _ ≤ |b| * (2 / ‖1 - z‖) := mul_le_mul_of_nonneg_left hg (abs_nonneg _)
      _ = _ := by ring

/-- Sum the centered channel over ordered pairs; both signs are controlled. -/
private theorem centered_channel (s : Finset ℕ) (a : ℕ → ℝ) (r : ℕ → ℕ → ℂ)
    (hr : ∀ p ∈ s, ∀ q ∈ s, ‖r p q‖ = 1) (M : ℤ) (K : ℕ) :
    |(∑ p ∈ s, ∑ q ∈ s, ∑ j ∈ Finset.range K,
        (((a p * a q : ℝ) : ℂ) * r p q ^ (M + (j : ℤ))).re) -
      (K : ℝ) * (∑ p ∈ s, ∑ q ∈ s, if r p q = 1 then a p * a q else 0)| ≤
      ∑ p ∈ s, ∑ q ∈ s,
        if r p q = 1 then 0 else 2 * |a p * a q| / ‖1 - r p q‖ := by
  classical
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ p ∈ s, |∑ q ∈ s,
          ((∑ j ∈ Finset.range K,
            (((a p * a q : ℝ) : ℂ) * r p q ^ (M + (j : ℤ))).re) -
              (K : ℝ) * (if r p q = 1 then a p * a q else 0))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ s, ∑ q ∈ s,
        |(∑ j ∈ Finset.range K,
          (((a p * a q : ℝ) : ℂ) * r p q ^ (M + (j : ℤ))).re) -
            (K : ℝ) * (if r p q = 1 then a p * a q else 0)| := by
      exact Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ _ := Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (fun q hq =>
      centered_geometric (hr p hp q hq) (a p * a q) M K))

/-- The new, unconjugated square expansion. The norm-square owner is imported. -/
private theorem square_expansion (s : Finset ℕ) (a : ℕ → ℝ) (z : ℕ → ℂ) (m : ℤ) :
    ((∑ p ∈ s, (a p : ℂ) * z p ^ m) ^ 2).re =
      ∑ p ∈ s, ∑ q ∈ s, (((a p * a q : ℝ) : ℂ) * (z p * z q) ^ m).re := by
  have ht (p q : ℕ) :
      ((a p : ℂ) * z p ^ m) * ((a q : ℂ) * z q ^ m) =
        ((a p * a q : ℝ) : ℂ) * (z p * z q) ^ m := by
    rw [mul_zpow, Complex.ofReal_mul]
    ring
  rw [pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum, ht]
  simp only [map_sum Complex.reAddGroupHom]

private theorem sine_energy_identity (c : ℕ) (m : ℤ) :
    2 * primeSymbol c m ^ 2 =
      ‖∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m‖ ^ 2 -
      ((∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m) ^ 2).re := by
  rw [primeSymbol_is_im]
  let E : ℂ := ∑ q ∈ primeIndices c, (primeWeight q : ℂ) * primePhase c q ^ m
  change 2 * E.im ^ 2 = ‖E‖ ^ 2 - (E ^ 2).re
  have hn := Complex.sq_norm_sub_sq_im E
  simp only [pow_two, Complex.mul_re] at hn ⊢
  nlinarith

/-- Exact mean, with integer block start, K=0, all prime powers and self-pairs. -/
theorem prime_symbol_exact_block {c : ℕ} (hc : 2 ≤ c) (M : ℤ) (K : ℕ) :
    |(∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) -
      (K : ℝ) * mean c| ≤ offset c := by
  classical
  let s := primeIndices c
  let E (m : ℤ) : ℂ := ∑ q ∈ s, (primeWeight q : ℂ) * primePhase c q ^ m
  have hdiff := centered_channel s primeWeight
    (fun p q => primePhase c p * conj (primePhase c q))
    (fun p _ q _ => by simp [norm_mul, primePhase_norm]) M K
  have hsum := centered_channel s primeWeight
    (fun p q => primePhase c p * primePhase c q)
    (fun p _ q _ => by simp [norm_mul, primePhase_norm]) M K
  have hdres (p : ℕ) (hp : p ∈ s) (q : ℕ) (hq : q ∈ s) :
      (primePhase c p * conj (primePhase c q) = 1) = (p = q) :=
    propext (difference_resonance hc hp hq)
  have hsres (p : ℕ) (hp : p ∈ s) (q : ℕ) (hq : q ∈ s) :
      (primePhase c p * primePhase c q = 1) = (p * q = c) :=
    propext (sum_resonance hc hp hq)
  have hD : (∑ p ∈ s, ∑ q ∈ s,
      if primePhase c p * conj (primePhase c q) = 1 then primeWeight p * primeWeight q else 0)
      = primeSquareMass c := by
    calc
      _ = ∑ p ∈ s, ∑ q ∈ s, if p = q then primeWeight p * primeWeight q else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        rw [hdres p hp q hq]
      _ = primeSquareMass c := by
        unfold primeSquareMass
        apply Finset.sum_congr rfl
        intro p hp
        simp [hp, pow_two]
  have hCd : (∑ p ∈ s, ∑ q ∈ s,
      if primePhase c p * conj (primePhase c q) = 1 then 0 else
        2 * |primeWeight p * primeWeight q| / ‖1 - primePhase c p * conj (primePhase c q)‖)
      = primeCross c := by
    unfold primeCross orderedCross
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hdres p hp q hq]
  have hR : (∑ p ∈ s, ∑ q ∈ s,
      if primePhase c p * primePhase c q = 1 then primeWeight p * primeWeight q else 0)
      = resonantMass c := by
    unfold resonantMass
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsres p hp q hq]
  have hCs : (∑ p ∈ s, ∑ q ∈ s,
      if primePhase c p * primePhase c q = 1 then 0 else
        2 * |primeWeight p * primeWeight q| / ‖1 - primePhase c p * primePhase c q‖)
      = sumCross c := by
    unfold sumCross
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [hsres p hp q hq]
  have hX : (∑ j ∈ Finset.range K, ‖E (M + (j : ℤ))‖ ^ 2) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ j ∈ Finset.range K,
        (((primeWeight p * primeWeight q : ℝ) : ℂ) *
          (primePhase c p * conj (primePhase c q)) ^ (M + (j : ℤ))).re := by
    simp only [E, norm_square_expansion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  have hY : (∑ j ∈ Finset.range K, (E (M + (j : ℤ)) ^ 2).re) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ j ∈ Finset.range K,
        (((primeWeight p * primeWeight q : ℝ) : ℂ) *
          (primePhase c p * primePhase c q) ^ (M + (j : ℤ))).re := by
    simp only [E, square_expansion]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _
    rw [Finset.sum_comm]
  rw [hD, hCd, ← hX] at hdiff
  rw [hR, hCs, ← hY] at hsum
  have henergy :
      2 * (∑ j ∈ Finset.range K, primeSymbol c (M + (j : ℤ)) ^ 2) =
        (∑ j ∈ Finset.range K, ‖E (M + (j : ℤ))‖ ^ 2) -
        (∑ j ∈ Finset.range K, (E (M + (j : ℤ)) ^ 2).re) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => sine_energy_identity c _)
  obtain ⟨hdlo, hdhi⟩ := abs_le.mp hdiff
  obtain ⟨hslo, hshi⟩ := abs_le.mp hsum
  apply abs_le.mpr
  dsimp [mean, offset]
  constructor <;> nlinarith [henergy]

theorem offset_nonneg (c : ℕ) : 0 ≤ offset c := by
  have hd : 0 ≤ primeCross c := by
    unfold primeCross orderedCross
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro q _
    split_ifs <;> positivity
  have hs : 0 ≤ sumCross c := by
    unfold sumCross
    apply Finset.sum_nonneg
    intro p _
    apply Finset.sum_nonneg
    intro q _
    split_ifs <;> positivity
  exact div_nonneg (add_nonneg hd hs) (by norm_num)

/-- Nonnegativity is derived from actual nonnegative blocks at every K. -/
theorem mean_nonneg {c : ℕ} (hc : 2 ≤ c) : 0 ≤ mean c := by
  by_contra h
  have hneg : mean c < 0 := lt_of_not_ge h
  obtain ⟨K, hK⟩ := exists_nat_gt (offset c / (-mean c))
  have hmul : offset c < (K : ℝ) * (-mean c) :=
    (div_lt_iff₀ (neg_pos.mpr hneg)).mp hK
  have hb := (abs_le.mp (prime_symbol_exact_block hc 0 K)).2
  have hnon : 0 ≤ ∑ j ∈ Finset.range K, primeSymbol c (0 + (j : ℤ)) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

/-- Square-root multiplicativity is the only multiplicativity used here. -/
private theorem resonant_weight {c p q : ℕ} (hpq : p * q = c) :
    primeWeight p * primeWeight q =
      (ArithmeticFunction.vonMangoldt p * ArithmeticFunction.vonMangoldt q) /
        Real.sqrt (c : ℝ) := by
  have hs : Real.sqrt (c : ℝ) = Real.sqrt (p : ℝ) * Real.sqrt (q : ℝ) := by
    rw [← hpq, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg p)]
  rw [primeWeight, primeWeight, hs, div_mul_div_comm]

/-- Identification with the actual ArithmeticFunction Dirichlet convolution.
The two discarded divisor endpoints vanish because Lambda(1)=0. -/
theorem resonantMass_eq_convolution {c : ℕ} (hc : 2 ≤ c) :
    resonantMass c =
      ((ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c) /
        Real.sqrt (c : ℝ) := by
  classical
  have hc0 : c ≠ 0 := by omega
  let s := primeIndices c ×ˢ primeIndices c
  have hfilter : s.filter (fun x => x.1 * x.2 = c) =
      c.divisorsAntidiagonal.filter (fun x => 2 ≤ x.1 ∧ 2 ≤ x.2) := by
    ext x
    obtain ⟨p, q⟩ := x
    simp only [s, Finset.mem_filter, Finset.mem_product, primeIndices,
      Finset.mem_Ico, Nat.mem_divisorsAntidiagonal, hc0, and_true]
    constructor
    · rintro ⟨⟨⟨hp, _⟩, ⟨hq, _⟩⟩, hpq⟩
      exact ⟨hpq, hp, hq⟩
    · rintro ⟨hpq, hp, hq⟩
      have hpl : p < c := by
        have hb := Nat.mul_le_mul_left p hq
        omega
      have hql : q < c := by
        have hb := Nat.mul_le_mul_right q hp
        omega
      exact ⟨⟨⟨hp, hpl⟩, ⟨hq, hql⟩⟩, hpq⟩
  have hpad :
      (∑ x ∈ c.divisorsAntidiagonal.filter (fun x => 2 ≤ x.1 ∧ 2 ≤ x.2),
        primeWeight x.1 * primeWeight x.2) =
      ∑ x ∈ c.divisorsAntidiagonal, primeWeight x.1 * primeWeight x.2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro x hx hnot
    have hpos := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
    have hsmall : x.1 = 1 ∨ x.2 = 1 := by
      have hn : ¬ (2 ≤ x.1 ∧ 2 ≤ x.2) := by
        intro hh
        exact hnot (Finset.mem_filter.mpr ⟨hx, hh⟩)
      omega
    rcases hsmall with hleft | hright
    · simp [primeWeight, hleft]
    · simp [primeWeight, hright]
  calc
    resonantMass c = ∑ x ∈ s.filter (fun x => x.1 * x.2 = c),
        primeWeight x.1 * primeWeight x.2 := by
      rw [Finset.sum_filter, Finset.sum_product]
      rfl
    _ = ∑ x ∈ c.divisorsAntidiagonal, primeWeight x.1 * primeWeight x.2 := by
      rw [hfilter, hpad]
    _ = ∑ x ∈ c.divisorsAntidiagonal,
        (ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2) /
          Real.sqrt (c : ℝ) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact resonant_weight (Nat.mem_divisorsAntidiagonal.mp hx).1
    _ = _ := by rw [← Finset.sum_div, ArithmeticFunction.mul_apply]

theorem mean_eq_convolution {c : ℕ} (hc : 2 ≤ c) :
    mean c = (primeSquareMass c -
      (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c /
        Real.sqrt (c : ℝ)) / 2 := by
  rw [mean, resonantMass_eq_convolution hc]

/-- Three distinct prime factors cannot be supplied by two supported Lambda factors. -/
theorem convolution_zero_of_three_primeFactors {c : ℕ}
    (hcard : 3 ≤ c.primeFactors.card) :
    (ArithmeticFunction.vonMangoldt * ArithmeticFunction.vonMangoldt) c = 0 := by
  classical
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  by_cases hp : ArithmeticFunction.vonMangoldt x.1 = 0
  · rw [hp, zero_mul]
  by_cases hq : ArithmeticFunction.vonMangoldt x.2 = 0
  · rw [hq, mul_zero]
  have hpc := isPrimePow_iff_card_primeFactors_eq_one.mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hp)
  have hqc := isPrimePow_iff_card_primeFactors_eq_one.mp
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hq)
  obtain ⟨hprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  obtain ⟨hp0, hq0⟩ := Nat.ne_zero_of_mem_divisorsAntidiagonal hx
  have hmul := Nat.primeFactors_mul hp0 hq0
  have hle := Finset.card_union_le x.1.primeFactors x.2.primeFactors
  rw [hprod] at hmul
  rw [← hmul, hpc, hqc] at hle
  omega

theorem mean_of_three_primeFactors {c : ℕ} (hc : 2 ≤ c)
    (hcard : 3 ≤ c.primeFactors.card) : mean c = primeSquareMass c / 2 := by
  rw [mean_eq_convolution hc, convolution_zero_of_three_primeFactors hcard, zero_div, sub_zero]

/-- Same generic Abel helper and inverse-square comparison as T2; no new Abel proof. -/
private theorem tail_partial {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (K : ℕ) :
    (∑ j ∈ Finset.range K,
      primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ≤
        tailBudget c N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hA (k : ℕ) :
      (∑ j ∈ Finset.range k, primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2) ≤
        (k : ℝ) * mean c + offset c := by
    have hb := (abs_le.mp (prime_symbol_exact_block hc ((N : ℤ) + 1) k)).2
    have he : ∀ j : ℕ, (N : ℤ) + 1 + (j : ℤ) = ((N + j + 1 : ℕ) : ℤ) := by
      intro j
      push_cast
      ring
    simp_rw [he] at hb
    linarith
  have hab := finite_abel_majorant
    (fun j => primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2) (inverseSquareWeight N)
    (mean c) (offset c) (offset_nonneg c) (fun _ => sq_nonneg _)
    (inverseSquareWeight_antitone hN) hA K
  have hw : (∑ j ∈ Finset.range K, inverseSquareWeight N j) ≤ (N : ℝ)⁻¹ :=
    D5.S3.Weil.ZetaBridge.WeilInfiniteComplementLeakage.inverse_square_partial_le hNR K
  calc
    _ ≤ mean c * (∑ j ∈ Finset.range K, inverseSquareWeight N j) +
        offset c * inverseSquareWeight N 0 := hab
    _ ≤ mean c * (N : ℝ)⁻¹ + offset c * inverseSquareWeight N 0 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hw (mean_nonneg hc)) _
    _ = _ := by simp [tailBudget, inverseSquareWeight, div_eq_mul_inv, inv_pow]

/-- Actual convergent tail: j ↦ N+j+1 enumerates every m>N exactly once. -/
theorem prime_symbol_square_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) :
    Summable (fun j : ℕ =>
      primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ∧
    (∑' j : ℕ, primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j) ≤
      tailBudget c N := by
  have hnon (j : ℕ) :
      0 ≤ primeSymbol c ((N + j + 1 : ℕ) : ℤ) ^ 2 * inverseSquareWeight N j :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  exact ⟨summable_of_sum_range_le hnon (tail_partial hc hN),
    Real.tsum_le_of_sum_range_le hnon (tail_partial hc hN)⟩

/-- Arbitrary complex beta, retaining its norm squared exactly. -/
theorem complex_prime_tail {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N) (β : ℂ) :
    Summable (fun j : ℕ =>
      ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧
    (∑' j : ℕ,
      ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
        ‖β‖ ^ 2 * tailBudget c N := by
  obtain ⟨hs, hb⟩ := prime_symbol_square_tail hc hN
  constructor
  · exact (hs.mul_left (‖β‖ ^ 2)).congr (fun j => (complex_prime_energy c N j β).symm)
  · simp_rw [complex_prime_energy]
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (sq_nonneg _)

/-- Live sine-tail specialization, consumed again by the physical module. -/
theorem complex_prime_tail_three_primeFactors {c N : ℕ} (hc : 2 ≤ c) (hN : 0 < N)
    (hcard : 3 ≤ c.primeFactors.card) (β : ℂ) :
    Summable (fun j : ℕ =>
      ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧
    (∑' j : ℕ,
      ‖β * (primeSymbol c ((N + j + 1 : ℕ) : ℤ) : ℂ) / ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
        ‖β‖ ^ 2 * (primeSquareMass c / 2 / (N : ℝ) + offset c / ((N : ℝ) + 1) ^ 2) := by
  simpa only [tailBudget, mean_of_three_primeFactors hc hcard] using complex_prime_tail hc hN β

/-- Positive multiples inherit the generic class; no all-Robin-input assertion. -/
theorem three_primeFactors_of_multiple {d c : ℕ} (hd : 3 ≤ d.primeFactors.card)
    (hdc : d ∣ c) (hc0 : c ≠ 0) : 3 ≤ c.primeFactors.card :=
  hd.trans (Finset.card_le_card (Nat.primeFactors_mono hdc hc0))

/-- A small divisibility certificate, subsequently consumed by a genuine tail. -/
private theorem card_5040 : 3 ≤ (5040 : ℕ).primeFactors.card := by
  have hsub : ({2, 3, 5} : Finset ℕ) ⊆ (5040 : ℕ).primeFactors := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;>
      exact Nat.mem_primeFactors.mpr ⟨by norm_num, by norm_num, by norm_num⟩
  have h := Finset.card_le_card hsub
  have hs : ({2, 3, 5} : Finset ℕ).card = 3 := by decide
  rwa [hs] at h

/-- Actual complex sine tail at every positive multiple of the 5040 scale. -/
theorem complex_prime_tail_multiple_5040 {k N : ℕ} (hk : 0 < k) (hN : 0 < N) (β : ℂ) :
    Summable (fun j : ℕ =>
      ‖β * (primeSymbol (5040 * k) ((N + j + 1 : ℕ) : ℤ) : ℂ) /
        ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ∧
    (∑' j : ℕ,
      ‖β * (primeSymbol (5040 * k) ((N + j + 1 : ℕ) : ℤ) : ℂ) /
        ((N + j + 1 : ℕ) : ℂ)‖ ^ 2) ≤
      ‖β‖ ^ 2 * (primeSquareMass (5040 * k) / 2 / (N : ℝ) +
        offset (5040 * k) / ((N : ℝ) + 1) ^ 2) := by
  have hc : 2 ≤ 5040 * k := by nlinarith
  exact complex_prime_tail_three_primeFactors hc hN
    (three_primeFactors_of_multiple card_5040 (show 5040 ∣ 5040 * k from ⟨k, rfl⟩)
      (Nat.mul_ne_zero (by norm_num) (Nat.ne_of_gt hk))) β

/-- Empty endpoint scale, including all constants in the exact theorem. -/
theorem cutoff_two : primeSymbol 2 = 0 ∧ primeSquareMass 2 = 0 ∧
    resonantMass 2 = 0 ∧ mean 2 = 0 ∧ offset 2 = 0 := by
  simp [primeSymbol, primeIndices, primeSquareMass, resonantMass, mean, offset,
    primeCross, orderedCross, sumCross]

/-- The zero interior lattice mode is retained and contributes zero sine. -/
theorem primeSymbol_zero (c : ℕ) : primeSymbol c 0 = 0 := by
  simp [primeSymbol]

end D5.S3.Weil.ZetaBridge.PrimeSymbolResonance
