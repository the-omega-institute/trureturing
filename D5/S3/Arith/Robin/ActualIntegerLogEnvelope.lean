/- GID: D5/S3/Arith/Robin/ActualIntegerLogEnvelope
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/ActualIntegerLogEnvelope
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: Fixed-price integer optimizers give arbitrary-error actual Robin envelopes. -/

import D5.S3.Arith.Robin.OriginalFirstClockTransport
import D5.S3.Arith.Robin.EulerLayerInventoryGrowth
import D5.S3.Arith.Robin.MertensExplicitEnvelope
import D5.S3.Weil.Mertens.CenteredTail
import D5.S3.Weil.GronwallUpperEnvelope

/-! The comparator alone has smooth support; global fixed-price optimality transfers its bound
to every positive target integer. The inventory size error is an arbitrary positive parameter. -/

noncomputable section

namespace D5.S3.Arith.Robin.ActualIntegerLogEnvelope

open Finset
open D5.S3.Arith.Robin.OriginalFirstClockTransport
open D5.S3.Arith.GoldenResourceOptimalInteger
open D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open D5.S3.Arith.Robin.EulerLayerInventoryGrowth

theorem supported_sigma_bound {U : ℕ} (hU : 0 < U) {x : ℝ}
    (hsupport : ∀ p ∈ U.primeFactors, (p : ℝ) ≤ x) :
    (ArithmeticFunction.sigma 1 U : ℝ) / U ≤
      ∏ p ∈ Ioc (0 : ℕ) ⌊x⌋₊ with p.Prime, (1 - 1 / (p : ℝ))⁻¹ := by
  have hgeom (p : ℕ) (hp : p.Prime) (a : ℕ) :
      (∑ i ∈ range (a + 1), (p : ℝ) ^ i) / (p : ℝ) ^ a ≤
        (1 - 1 / (p : ℝ))⁻¹ := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hpm : (0 : ℝ) < (p : ℝ) - 1 := sub_pos.mpr hp1
    have hpow : (0 : ℝ) < (p : ℝ) ^ a := pow_pos hp0 a
    rw [geom_sum_eq hp1.ne']
    calc
      _ ≤ (p : ℝ) ^ (a + 1) / (p - 1) / p ^ a :=
        div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right (sub_le_self _ zero_le_one) hpm.le) hpow.le
      _ = _ := by
        rw [pow_succ, div_right_comm, mul_div_cancel_left₀ _ hpow.ne',
          one_sub_div hp0.ne', inv_div]
  have hnprod : (U : ℝ) = ∏ p ∈ U.primeFactors, (p : ℝ) ^ U.factorization p := by
    exact_mod_cast Nat.prod_primeFactors_pow_factorization hU.ne'
  have hsigmaprod : (ArithmeticFunction.sigma 1 U : ℝ) =
      ∏ p ∈ U.primeFactors, ∑ i ∈ range (U.factorization p + 1), (p : ℝ) ^ i := by
    simpa only [Nat.cast_prod, Nat.cast_sum, Nat.cast_pow, mul_one] using
      congrArg (fun k : ℕ => (k : ℝ))
        (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul
          (k := 1) hU.ne')
  have hlocal : (ArithmeticFunction.sigma 1 U : ℝ) / U ≤
      ∏ p ∈ U.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [hsigmaprod, hnprod, ← prod_div_distrib]
    exact prod_le_prod₀
      (fun p _ => div_nonneg (sum_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg p) i)
        (pow_nonneg (Nat.cast_nonneg p) _))
      (fun p hp => hgeom p (Nat.prime_of_mem_primeFactors hp) _)
  have hf : U.primeFactors.filter (fun p : ℕ => (p : ℝ) ≤ x) = U.primeFactors :=
    filter_eq_self.mpr hsupport
  exact hlocal.trans (by
    simpa only [hf] using D5.S3.Weil.GronwallUpperEnvelope.small_prime_product_le U x)

private theorem strict_support {x : ℝ} (hx : 1 < x) {U : ℕ} (hU : 0 < U)
    (hstrict : ∀ p : ℕ, p.Prime →
      U.factorization p = optimalLayerCount (1 / (x * Real.log x)) p) :
    ∀ p ∈ U.primeFactors, (p : ℝ) ≤ x := by
  intro p hpU
  have hp := Nat.prime_of_mem_primeFactors hpU
  have ha := hp.factorization_pos_of_dvd hU.ne' (Nat.dvd_of_mem_primeFactors hpU)
  have hb := active_power_bound hx hstrict hp (k := 1) le_rfl ha
  simp only [pow_one] at hb
  by_contra h
  have hxp : x ≤ (p : ℝ) := (lt_of_not_ge h).le
  have hmul : x * Real.log x ≤ (p : ℝ) * Real.log p :=
    mul_le_mul hxp (Real.log_le_log (by linarith) hxp) (Real.log_pos hx).le
      (Nat.cast_nonneg p)
  linarith

private theorem eventual_envelope_of_prime_product {B c : ℝ} (hB : 286 ≤ B)
    (hproduct : ∀ x : ℝ, B ≤ x →
      (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ ≤
        Real.exp Real.eulerMascheroniConstant * Real.log x * Real.exp (c / Real.log x))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 286 ≤ A ∧ ∀ n : ℕ, 0 < n → A ≤ Real.log (n : ℝ) →
      originalObjective n - Real.eulerMascheroniConstant ≤
        (c + epsilon) / Real.log (Real.log (n : ℝ)) := by
  obtain ⟨T, hT, hgrowth⟩ := strict_inventory_uniform_growth epsilon hepsilon
  refine ⟨max T B, hB.trans (le_max_right _ _), ?_⟩
  intro n hn hlarge
  let X := Real.log (n : ℝ)
  have hX : 286 ≤ X := hB.trans ((le_max_right T B).trans hlarge)
  have hX1 : 1 < X := by linarith
  have hX0 : 0 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1
  let lam := 1 / (X * Real.log X)
  have hlam : 0 < lam := one_div_pos.mpr (mul_pos hX0 hL)
  obtain ⟨U, hU, hcount, hopt, _⟩ := optimal_layer_count_spec hlam
  have hstrict : ∀ p : ℕ, p.Prime →
      U.factorization p = optimalLayerCount (1 / (X * Real.log X)) p :=
    fun p _ => hcount p
  have hnear := hgrowth X ((le_max_left T B).trans hlarge) U (by omega) hstrict
  have hratio : 1 - Real.log (U : ℝ) / X ≤ epsilon := by
    linarith [abs_lt.mp hnear |>.1]
  have hs := supported_sigma_bound (by omega : 0 < U)
    (strict_support hX1 (by omega) hstrict)
  have hm := hproduct X ((le_max_right T B).trans hlarge)
  rw [← prod_inv_distrib] at hm
  have hpos : 0 < (ArithmeticFunction.sigma 1 U : ℝ) / U :=
    div_pos (by exact_mod_cast ArithmeticFunction.sigma_pos 1 U (by omega))
      (by exact_mod_cast (by omega : 0 < U))
  have hlog := Real.log_le_log hpos (hs.trans hm)
  rw [Real.log_mul (mul_pos (Real.exp_pos _) hL).ne' (Real.exp_pos _).ne',
    Real.log_mul (Real.exp_pos _).ne' hL.ne', Real.log_exp, Real.log_exp] at hlog
  have hcompare := hopt n (by omega)
  rw [golden_resource_sigma_identity lam (by omega),
    golden_resource_sigma_identity lam hU] at hcompare
  have hcost : lam * Real.log (n : ℝ) - lam * Real.log (U : ℝ) =
      (1 - Real.log (U : ℝ) / X) / Real.log X := by
    change (1 / (X * Real.log X)) * X - _ = _
    dsimp [lam]
    field_simp
    <;> ring
  have hcostle := div_le_div_of_nonneg_right hratio hL.le
  change Real.log ((ArithmeticFunction.sigma 1 n : ℝ) / n) -
    Real.log (Real.log X) - Real.eulerMascheroniConstant ≤
      ((c) + epsilon) / Real.log X
  have hid : (c) / Real.log X + epsilon / Real.log X =
      ((c) + epsilon) / Real.log X := by ring
  linarith

/-- The strict inventory transfers its arbitrary positive size error to every actual
positive integer. Only the comparator has smooth support. -/
theorem eventual_actual_integer_envelope_epsilon (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 286 ≤ A ∧ ∀ n : ℕ, 0 < n → A ≤ Real.log (n : ℝ) →
      originalObjective n - Real.eulerMascheroniConstant ≤
        ((19 / 10 : ℝ) + epsilon) / Real.log (Real.log (n : ℝ)) := by
  exact eventual_envelope_of_prime_product (B := 286) le_rfl
    (fun _ hx => MertensExplicitEnvelope.prime_product_upper_effective hx)
    epsilon hepsilon

/-- Every positive error coefficient eventually bounds the original objective on all
positive integers, with the cutoff chosen before the integer. -/
theorem eventual_actual_integer_envelope_small_error (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ A : ℝ, 286 ≤ A ∧ ∀ n : ℕ, 0 < n → A ≤ Real.log (n : ℝ) →
      originalObjective n - Real.eulerMascheroniConstant ≤
        epsilon / Real.log (Real.log (n : ℝ)) := by
  have htail := D5.S3.Weil.Mertens.CenteredTail.E2p_isLittleO_inv_log.bound
    (half_pos hepsilon)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp htail
  have hproduct (x : ℝ) (hx : max B 286 ≤ x) :
      (∏ p ∈ Ioc 0 ⌊x⌋₊ with p.Prime, (1 - (1 : ℝ) / p))⁻¹ ≤
        Real.exp Real.eulerMascheroniConstant * Real.log x *
          Real.exp ((epsilon / 2) / Real.log x) := by
    have hx286 : 286 ≤ x := (le_max_right B 286).trans hx
    have hlog : 0 < Real.log x := Real.log_pos (by linarith)
    have hbound : _root_.Mertens.E₂p x ≤ (epsilon / 2) / Real.log x := by
      have hb := hB x ((le_max_left B 286).trans hx)
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (one_div_pos.mpr hlog)] at hb
      exact (le_abs_self _).trans (by simpa only [div_eq_mul_inv, one_mul] using hb)
    have hsign := MertensExplicitEnvelope.mertens_E3_ge_neg_E2p x
    rw [_root_.Mertens.prod_one_minus_div_prime_eq (by linarith : 1 < x)]
    calc
      _ = Real.exp Real.eulerMascheroniConstant * Real.log x *
          Real.exp (-_root_.Mertens.E₃ x) := by
        simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, ← Real.exp_neg, neg_neg]
        ring
      _ ≤ _ := by
        gcongr
        linarith
  have h := eventual_envelope_of_prime_product (le_max_right B 286)
    hproduct (epsilon / 2) (half_pos hepsilon)
  simpa only [add_halves] using h

/-- Every sufficiently large actual integer satisfies the coefficient-two logarithmic
envelope. Smooth support is used only for a separate strict fixed-price optimizer. -/
theorem eventual_actual_integer_envelope :
    ∃ A : ℝ, 286 ≤ A ∧ ∀ n : ℕ, 0 < n → A ≤ Real.log (n : ℝ) →
      originalObjective n - Real.eulerMascheroniConstant ≤
        2 / Real.log (Real.log (n : ℝ)) := by
  simpa only [show (19 / 10 : ℝ) + 1 / 10 = 2 by norm_num] using
    eventual_actual_integer_envelope_epsilon (1 / 10) (by norm_num)

#print axioms eventual_actual_integer_envelope_small_error

#print axioms eventual_actual_integer_envelope_epsilon

#print axioms eventual_actual_integer_envelope

end D5.S3.Arith.Robin.ActualIntegerLogEnvelope
