/-
Full natural-order coverage by complete strict and weak prime-layer inventories.
A positive two-adic seed bounds the actual activation prices. The next-event
product identity and maximal qualifying price give the bracket without a
growth, cofinality or coverage premise. All simultaneous ties are retained.
-/

import D5.S3.Arith.Robin.ActualTwoPriceDefect
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

noncomputable section

namespace D5.S3.Arith.Robin.ActualGlobalBracketing

open Finset
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.GoldenResource.GoldenResourceThresholdCriterion
open D5.S3.Arith.Robin.ActualTwoPriceDefect

/-- Global optimality of the original chosen strict integer. -/
theorem strict_is_optimal {q : ℝ} (hq : 0 < q) :
    IsGoldenResourceOptimal q (strictInteger q) := by
  simpa only [strictInteger, dite_eq_left hq] using
    (Classical.choose_spec (optimal_layer_count_spec hq)).2.2.1

/-- Exact weak membership, including every equality layer. -/
theorem weak_layer_iff {q : ℝ} (hq : 0 < q) {p k : ℕ}
    (hp : p.Prime) (hk : 1 ≤ k) :
    k ≤ (maximalInteger q).factorization p ↔ q ≤ goldenLayerMarginal p k := by
  rw [(maximalInteger_spec hq).2.1 p]
  have he := weak_layers_eq_count_interval hq hp
  have hm : (1 ≤ k ∧ p.Prime ∧ q ≤ goldenLayerMarginal p k) ↔
      k ∈ Set.Icc 1 (weakLayerCount q p) := by rw [← he]; rfl
  simpa only [Set.mem_Icc, hk, hp, true_and] using hm.symm

/-- Positivity proof reused from the private `marginal_pos` in the sealed
GoldenResourcePriceInterval source. No distribution estimate is needed. -/
theorem layer_marginal_pos {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    0 < goldenLayerMarginal p k := by
  have hpPos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hiPos : 0 < (p : ℝ)⁻¹ := inv_pos.mpr hpPos
  have hiLt : (p : ℝ)⁻¹ < 1 :=
    (inv_lt_one₀ hpPos).mpr (by exact_mod_cast hp.one_lt)
  have hden : 0 < 1 - (p : ℝ)⁻¹ ^ k :=
    sub_pos.mpr (pow_lt_one₀ hiPos.le hiLt (by omega))
  have hpow : (p : ℝ)⁻¹ ^ (k + 1) < (p : ℝ)⁻¹ ^ k :=
    pow_lt_pow_right_of_lt_one₀ hiPos hiLt (by omega)
  unfold goldenLayerMarginal
  apply div_pos _ (Real.log_pos (by exact_mod_cast hp.one_lt))
  apply Real.log_pos
  exact (one_lt_div hden).mpr (by linarith)

/-- All DISTINCT actual activation values at or above a positive seed. -/
def activationPrices (ε : ℝ) (hε : 0 < ε) : Finset ℝ :=
  (weak_layers_finite hε).toFinset.image
    (fun pk => goldenLayerMarginal pk.1 pk.2)

theorem mem_activationPrices {ε r : ℝ} (hε : 0 < ε) :
    r ∈ activationPrices ε hε ↔
      ∃ p k : ℕ, 1 ≤ k ∧ p.Prime ∧ ε ≤ goldenLayerMarginal p k ∧
        goldenLayerMarginal p k = r := by
  classical
  constructor
  · intro hr
    obtain ⟨⟨p, k⟩, hpk, heq⟩ := Finset.mem_image.mp hr
    have h := (weak_layers_finite hε).mem_toFinset.mp hpk
    exact ⟨p, k, h.1, h.2.1, h.2.2, heq⟩
  · rintro ⟨p, k, hk, hp, hgain, heq⟩
    exact Finset.mem_image.mpr ⟨(p, k),
      (weak_layers_finite hε).mem_toFinset.mpr ⟨hk, hp, hgain⟩, heq⟩

theorem activationPrices_ge {ε r : ℝ} (hε : 0 < ε)
    (hr : r ∈ activationPrices ε hε) : ε ≤ r := by
  obtain ⟨p, k, _, _, hgain, rfl⟩ := (mem_activationPrices hε).mp hr
  exact hgain

/-- The weak product at the next actual event is the ENTIRE current
strict product. This proves full prime-by-prime factorization equality,
not a prefix estimate, subproduct bound or one-prime transition. -/
theorem next_event_product {ε q : ℝ} (hε : 0 < ε) (hεq : ε ≤ q)
    (hlarge : 1 < strictInteger q) :
    ∃ r ∈ activationPrices ε hε, q < r ∧
      maximalInteger r = strictInteger q := by
  classical
  have hq : 0 < q := hε.trans_le hεq
  have hactive : ∃ p k : ℕ, 1 ≤ k ∧ p.Prime ∧ q < goldenLayerMarginal p k := by
    by_contra hnone
    have hone : strictInteger q = 1 := by
      apply Nat.eq_of_factorization_eq
        (by have := strictInteger_pos hq; omega) (by omega)
      intro p
      by_cases hp : p.Prime
      · have hz : (strictInteger q).factorization p = 0 := by
          by_contra hz
          have hk : 1 ≤ (strictInteger q).factorization p := by omega
          exact hnone ⟨p, (strictInteger q).factorization p, hk, hp,
            (strict_layer_iff hq hp hk).mp le_rfl⟩
        simp [hz]
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    omega
  obtain ⟨p, k, hk, hp, hgain⟩ := hactive
  let T := (activationPrices ε hε).filter (fun r => q < r)
  have hT : T.Nonempty := by
    refine ⟨goldenLayerMarginal p k, Finset.mem_filter.mpr ⟨?_, hgain⟩⟩
    exact (mem_activationPrices hε).mpr ⟨p, k, hk, hp,
      hεq.trans hgain.le, rfl⟩
  obtain ⟨r, hr, hmin⟩ := T.exists_min_image id hT
  have hrE := (Finset.mem_filter.mp hr).1
  have hqr : q < r := (Finset.mem_filter.mp hr).2
  have hr0 : 0 < r := hq.trans hqr
  have hiff (p k : ℕ) (hp : p.Prime) (hk : 1 ≤ k) :
      k ≤ (maximalInteger r).factorization p ↔
        k ≤ (strictInteger q).factorization p := by
    rw [weak_layer_iff hr0 hp hk, strict_layer_iff hq hp hk]
    constructor
    · exact fun h => hqr.trans_le h
    · intro h
      apply hmin (goldenLayerMarginal p k)
      exact Finset.mem_filter.mpr ⟨(mem_activationPrices hε).mpr
        ⟨p, k, hk, hp, hεq.trans h.le, rfl⟩, h⟩
  refine ⟨r, hrE, hqr, ?_⟩
  apply Nat.eq_of_factorization_eq
    (by have := (maximalInteger_spec hr0).1; omega)
    (by have := strictInteger_pos hq; omega)
  intro p
  by_cases hp : p.Prime
  · apply le_antisymm
    · by_cases hz : (maximalInteger r).factorization p = 0
      · simp [hz]
      · exact (hiff p _ hp (by omega)).mp le_rfl
    · by_cases hz : (strictInteger q).factorization p = 0
      · simp [hz]
      · exact (hiff p _ hp (by omega)).mpr le_rfl
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

private theorem self_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 0 < (2 : ℕ) ^ n := by positivity
    simp only [pow_succ, mul_two]
    omega

/-- A DERIVED seed, not an inventory-growth or cofinality hypothesis. -/
theorem two_adic_seed {n : ℕ} (hn : 2 ≤ n) :
    let ε := goldenLayerMarginal 2 n
    0 < ε ∧ ε ∈ activationPrices ε (layer_marginal_pos Nat.prime_two (by omega)) ∧
      n ≤ maximalInteger ε := by
  dsimp only
  have hε : 0 < goldenLayerMarginal 2 n := layer_marginal_pos Nat.prime_two (by omega)
  refine ⟨hε, ?_, ?_⟩
  · exact (mem_activationPrices hε).mpr ⟨2, n, by omega, Nat.prime_two, le_rfl, rfl⟩
  · have hM := (maximalInteger_spec hε).1
    have hd : 2 ^ n ∣ maximalInteger (goldenLayerMarginal 2 n) :=
      (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mpr
        ((weak_layer_iff hε Nat.prime_two (by omega)).mpr le_rfl)
    exact (self_le_two_pow n).trans (Nat.le_of_dvd (by omega) hd)

/-- PRIMARY NEW TARGET. Every natural integer n >= 2 is bracketed by the
actual complete strict and weak optimizers at one POSITIVE real price.
No finiteness, growth, optimizer-existence or bracketing premise is added. -/
theorem all_integer_bracketing (n : ℕ) (hn : 2 ≤ n) :
    ∃ q : ℝ, 0 < q ∧ strictInteger q ≤ n ∧ n ≤ maximalInteger q := by
  classical
  let ε := goldenLayerMarginal 2 n
  have hε : 0 < ε := layer_marginal_pos Nat.prime_two (by omega)
  have hseed := two_adic_seed hn
  let C := (activationPrices ε hε).filter (fun q => n ≤ maximalInteger q)
  have hC : C.Nonempty :=
    ⟨ε, Finset.mem_filter.mpr ⟨hseed.2.1, hseed.2.2⟩⟩
  obtain ⟨q, hqC, hmax⟩ := C.exists_max_image id hC
  have hqE := (Finset.mem_filter.mp hqC).1
  have hnM := (Finset.mem_filter.mp hqC).2
  have hεq : ε ≤ q := activationPrices_ge hε hqE
  have hq : 0 < q := hε.trans_le hεq
  refine ⟨q, hq, ?_, hnM⟩
  by_contra hbad
  have hnB : n < strictInteger q := by omega
  obtain ⟨r, hrE, hqr, heq⟩ := next_event_product hε hεq (by omega)
  have hrC : r ∈ C := Finset.mem_filter.mpr ⟨hrE, by rw [heq]; omega⟩
  have hrq : r ≤ q := hmax r hrC
  exact (not_lt_of_ge hrq) hqr

/-- Same-price inclusion and the cross-price inclusions used below retain
all prime directions and all positive layers. -/
theorem strict_dvd_weak {q : ℝ} (hq : 0 < q) :
    strictInteger q ∣ maximalInteger q := by
  apply (Nat.factorization_le_iff_dvd
    (by have := strictInteger_pos hq; omega)
    (by have := (maximalInteger_spec hq).1; omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : (strictInteger q).factorization p = 0
    · simp [hz]
    · have hk : 1 ≤ (strictInteger q).factorization p := by omega
      exact (weak_layer_iff hq hp hk).mpr ((strict_layer_iff hq hp hk).mp le_rfl).le
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem weak_dvd_weak {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q ≤ r) :
    maximalInteger r ∣ maximalInteger q := by
  apply (Nat.factorization_le_iff_dvd
    (by have := (maximalInteger_spec hr).1; omega)
    (by have := (maximalInteger_spec hq).1; omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : (maximalInteger r).factorization p = 0
    · simp [hz]
    · have hk : 1 ≤ (maximalInteger r).factorization p := by omega
      exact (weak_layer_iff hq hp hk).mpr
        (hqr.trans ((weak_layer_iff hr hp hk).mp le_rfl))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

theorem weak_dvd_strict {q r : ℝ} (hq : 0 < q) (hr : 0 < r) (hqr : q < r) :
    maximalInteger r ∣ strictInteger q := by
  apply (Nat.factorization_le_iff_dvd
    (by have := (maximalInteger_spec hr).1; omega)
    (by have := strictInteger_pos hq; omega)).mp
  intro p
  by_cases hp : p.Prime
  · by_cases hz : (maximalInteger r).factorization p = 0
    · simp [hz]
    · have hk : 1 ≤ (maximalInteger r).factorization p := by omega
      exact (strict_layer_iff hq hp hk).mpr
        (hqr.trans_le ((weak_layer_iff hr hp hk).mp le_rfl))
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The 5041 bracket is constructed by the theorem above. This is a
definition by a proved existence result, not an assumed boundary certificate. -/
def boundaryPrice : ℝ := Classical.choose (all_integer_bracketing 5041 (by omega))

theorem boundaryPrice_spec :
    0 < boundaryPrice ∧ strictInteger boundaryPrice ≤ 5041 ∧
      5041 ≤ maximalInteger boundaryPrice :=
  Classical.choose_spec (all_integer_bracketing 5041 (by omega))

/-- An exact symbolic finite cap. No numerical successor is asserted. -/
def boundaryCap : ℕ := maximalInteger boundaryPrice

theorem boundaryCap_ge : 5041 ≤ boundaryCap := boundaryPrice_spec.2.2

/-- Every interval crossing 5040 is contained in the stated finite region,
even if its lower endpoint is too small for the analytic log-log domain. -/
theorem crossing_interval_in_boundary {q : ℝ} (hq : 0 < q)
    (hB : strictInteger q ≤ 5040) {n : ℕ} (hn : n ≤ maximalInteger q) :
    n ≤ boundaryCap := by
  by_cases hqq : q < boundaryPrice
  · have hd := weak_dvd_strict hq boundaryPrice_spec.1 hqq
    have hle : boundaryCap ≤ strictInteger q :=
      Nat.le_of_dvd (by have := strictInteger_pos hq; omega) hd
    have := boundaryCap_ge
    omega
  · have hd := weak_dvd_weak boundaryPrice_spec.1 hq (le_of_not_gt hqq)
    have hle : maximalInteger q ≤ boundaryCap :=
      Nat.le_of_dvd (by have := boundaryCap_ge; omega) hd
    exact hn.trans hle

/-- Full natural-order coverage above the EXACT original boundary:
the finite region is retained, and every remaining integer has a genuine
same-price bracket whose lower endpoint is already above 5040. -/
theorem coverage_above_5040 {n : ℕ} (hn : 5040 < n) :
    n ≤ boundaryCap ∨ ∃ q : ℝ, 0 < q ∧ 5040 < strictInteger q ∧
      strictInteger q ≤ n ∧ n ≤ maximalInteger q := by
  by_cases hfinite : n ∈ Finset.Icc 5041 boundaryCap
  · exact Or.inl (Finset.mem_Icc.mp hfinite).2
  · have hnot : ¬ n ≤ boundaryCap := by
      intro hcap
      exact hfinite (Finset.mem_Icc.mpr ⟨by omega, hcap⟩)
    obtain ⟨q, hq, hBn, hnU⟩ := all_integer_bracketing n (by omega)
    have hB : 5040 < strictInteger q := by
      by_contra h
      exact hnot (crossing_interval_in_boundary hq (by omega) hnU)
    exact Or.inr ⟨q, hq, hB, hBn, hnU⟩

end D5.S3.Arith.Robin.ActualGlobalBracketing
