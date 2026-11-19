/- GID: D5/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive
   generality: I
   mirror-B: D5/B/S3/Arith/Abundancy/ZelinskyZhangDoublePrimitive
   mirror-E: none(waiver:symbolic-existence-no-numeric-artifact)
   anchors: []
   utility: none
   digest: Infinitely many integers are primitive non-deficient and KL-primitive. -/

import D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive
import D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity
import Mathlib.Analysis.Complex.ExponentialBounds

/-! A fixed prime interval aligns two distinct divisor thresholds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Finset Real Filter
open scoped BigOperators Topology
open D5.S3.Arith.Abundancy.ZelinskyZhangKLPrimitive

namespace D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive

/-- Non-deficiency with deficiency of every positive proper divisor. -/
def PrimitiveNonDeficient (n : ℕ) : Prop :=
  ¬ Deficient n ∧ ∀ d ∈ n.divisors, d < n → Deficient d

private lemma sigma_two (a : ℕ) :
    (ArithmeticFunction.sigma 1 (2 ^ a) : ℝ) = 2 * (2 : ℝ) ^ a - 1 := by
  rw [ArithmeticFunction.sigma_one_apply_prime_pow Nat.prime_two,
    Nat.geomSum_eq (m := 2) (by decide) (a + 1)]
  simp only [Nat.reduceSub, Nat.div_one]
  rw [Nat.cast_sub (by have := Nat.one_le_two_pow (n := a + 1); omega)]
  push_cast
  ring

private lemma kl_two (a : ℕ) : KL (2 ^ a) = -log 2 := by
  unfold KL
  rw [Nat.sum_divisors_prime_pow Nat.prime_two]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, ih, Nat.totient_prime_pow_succ Nat.prime_two]
    simp only [Nat.reduceSub, mul_one, Nat.cast_pow, Nat.cast_ofNat]
    rw [pow_succ]
    have h : (2 : ℝ) ^ a * 2 / (2 * 2 ^ a) = 1 := by field_simp
    rw [h, log_one, mul_zero, add_zero]

private lemma coprime_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    (2 ^ a).Coprime p :=
  (Nat.coprime_primes Nat.prime_two hp |>.mpr hp2.symm).pow_left a

private lemma sigma_two_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    (ArithmeticFunction.sigma 1 (2 ^ a * p) : ℝ) =
      (2 * (2 : ℝ) ^ a - 1) * (p + 1) := by
  change sig (2 ^ a * p) = _
  rw [Nat.mul_comm (2 ^ a) p, sig_prime_mul hp (coprime_two hp hp2 a).symm]
  change ((p : ℝ) + 1) * (ArithmeticFunction.sigma 1 (2 ^ a) : ℝ) = _
  rw [sigma_two]
  ring

private lemma kl_two_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a : ℕ) :
    KL (2 ^ a * p) = -((p : ℝ) + 1) * log 2 +
      p * (2 * (2 : ℝ) ^ a - 1) * log ((p : ℝ) / (p - 1)) := by
  rw [Nat.mul_comm (2 ^ a) p, kl_prime_mul hp (coprime_two hp hp2 a).symm, kl_two]
  change ((p : ℝ) + 1) * -log 2 +
    p * (ArithmeticFunction.sigma 1 (2 ^ a) : ℝ) * log ((p : ℝ) / (p - 1)) = _
  rw [sigma_two]
  ring

private lemma log_bounds {p : ℕ} (hp : 2 ≤ p) :
    1 / (p : ℝ) ≤ log ((p : ℝ) / (p - 1)) ∧
      log ((p : ℝ) / (p - 1)) ≤ 1 / ((p : ℝ) - 1) := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  refine ⟨?_, (D5.S3.Arith.Robin.FibonacciRankEulerTail.euler_log_bounds p hp).2⟩
  have hpm : (0 : ℝ) < p - 1 := by linarith
  have h := one_sub_inv_le_log_of_pos
    (div_pos (by positivity : (0 : ℝ) < p) hpm)
  have he : 1 - ((p : ℝ) / (p - 1))⁻¹ = 1 / (p : ℝ) := by
    field_simp
    ring
  simpa only [he] using h

private lemma proper_shapes {k p d : ℕ} (hp : p.Prime)
    (hd : d ∈ (2 ^ k * p).divisors) (hlt : d < 2 ^ k * p) :
    (∃ a ≤ k, d = 2 ^ a) ∨ (∃ a < k, d = 2 ^ a * p) := by
  rw [Nat.divisors_mul] at hd
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_mul.mp hd
  obtain ⟨a, ha, rfl⟩ := (Nat.mem_divisors_prime_pow Nat.prime_two k).mp hu
  rw [hp.divisors, mem_insert, mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact Or.inl ⟨a, ha, by simp⟩
  · refine Or.inr ⟨a, lt_of_le_of_ne ha ?_, rfl⟩
    intro he
    subst a
    exact (lt_irrefl _) hlt

private lemma double_primitive {k p : ℕ} (hk : 3 ≤ k) (hp : p.Prime)
    (hlo : 3 * 2 ^ k ≤ 2 * p) (hhi : 4 * p ≤ 7 * 2 ^ k) :
    PrimitiveNonDeficient (2 ^ k * p) ∧ KLPrimitive (2 ^ k * p) := by
  have hA : 8 ≤ 2 ^ k := (by norm_num : 8 = 2 ^ 3) ▸
    Nat.pow_le_pow_right (by decide : 0 < 2) hk
  have hp2 : p ≠ 2 := by omega
  have hAR : (8 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hA
  have hloR : 3 * (2 : ℝ) ^ k ≤ 2 * p := by exact_mod_cast hlo
  have hhiR : 4 * (p : ℝ) ≤ 7 * (2 : ℝ) ^ k := by exact_mod_cast hhi
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpm : (0 : ℝ) < p - 1 := by linarith
  have hloglo := (log_bounds hp.two_le).1
  have hloghi := (log_bounds hp.two_le).2
  have hlog2lo : (2 / 3 : ℝ) < log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2hi : log 2 < 1 := by linarith [Real.log_two_lt_d9]
  have hnondef : ¬ Deficient (2 ^ k * p) := by
    rw [Deficient, sigma_two_prime hp hp2]
    push_cast
    nlinarith
  have hkl : 0 < KL (2 ^ k * p) := by
    rw [kl_two_prime hp hp2]
    have hc : 0 < (p : ℝ) * (2 * (2 : ℝ) ^ k - 1) :=
      mul_pos (by positivity) (by linarith)
    have ht := mul_le_mul_of_nonneg_left hloglo hc.le
    have he : (p : ℝ) * (2 * (2 : ℝ) ^ k - 1) * (1 / p) =
        2 * (2 : ℝ) ^ k - 1 := by field_simp <;> ring
    rw [he] at ht
    have hn := mul_lt_mul_of_pos_left hlog2hi (by positivity : (0 : ℝ) < p + 1)
    nlinarith
  have proper (d : ℕ) (hd : d ∈ (2 ^ k * p).divisors)
      (hlt : d < 2 ^ k * p) : Deficient d ∧ KL d < 0 := by
    rcases proper_shapes hp hd hlt with ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩
    · constructor
      · rw [Deficient, sigma_two]
        push_cast
        linarith
      · rw [kl_two]
        linarith
    · have hpow : 2 * (2 : ℝ) ^ a ≤ (2 : ℝ) ^ k := by
        have h := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.succ_le_of_lt ha)
        have he : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
        rw [← he] at h
        exact_mod_cast h
      have hx : (1 : ℝ) ≤ (2 : ℝ) ^ a := one_le_pow₀ (by norm_num)
      constructor
      · rw [Deficient, sigma_two_prime hp hp2]
        push_cast
        nlinarith
      · rw [kl_two_prime hp hp2]
        have hc : 0 ≤ (p : ℝ) * (2 * (2 : ℝ) ^ a - 1) :=
          mul_nonneg (by positivity) (by linarith)
        have ht := mul_le_mul_of_nonneg_left hloghi hc
        have hfrac : (p : ℝ) * (2 * (2 : ℝ) ^ a - 1) / (p - 1) <
            (p + 1) * (2 / 3) := by
          apply (div_lt_iff₀ hpm).mpr
          have hprod := mul_nonneg (by positivity : (0 : ℝ) ≤ p)
            (sub_nonneg.mpr hloR)
          have hpowp := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ p)
          nlinarith
        have hn := mul_lt_mul_of_pos_left hlog2lo
          (by positivity : (0 : ℝ) < p + 1)
        rw [← div_eq_mul_one_div] at ht
        linarith
  exact ⟨⟨hnondef, fun d hd hlt => (proper d hd hlt).1⟩,
    hkl.le, fun d hd hlt => (proper d hd hlt).2⟩

private lemma eventually_prime_interval :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧
      (3 / 2 : ℝ) * x < p ∧ (p : ℝ) ≤ (7 / 4 : ℝ) * x := by
  obtain ⟨Y, hY⟩ :=
    D5.S3.Arith.Robin.PriceRecord.FixedLayerRigidity.fixed_cardinality_prime_window
      (A := (3 / 2 : ℝ)) (B := (7 / 4 : ℝ)) (by norm_num) (by norm_num) 1
  filter_upwards [eventually_ge_atTop Y] with x hx
  obtain ⟨S, hcard, hS⟩ := hY x hx
  have hnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨p, hp⟩ := hnonempty
  exact ⟨p, hS p hp⟩

/-- Question 1: positive integers with both primitive properties are unbounded. -/
theorem result : ∀ B : ℕ, ∃ n : ℕ,
    B < n ∧ 0 < n ∧ PrimitiveNonDeficient n ∧ KLPrimitive n := by
  intro B
  have hpow : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  obtain ⟨K, hK⟩ := eventually_atTop.mp (hpow.eventually eventually_prime_interval)
  let k := max K (B + 3)
  have hkK : K ≤ k := le_max_left _ _
  have hkB : B + 3 ≤ k := le_max_right _ _
  obtain ⟨p, hp, hlo, hhi⟩ := hK k hkK
  have hloN : 3 * 2 ^ k ≤ 2 * p := by
    exact_mod_cast (by nlinarith : 3 * (2 : ℝ) ^ k ≤ 2 * p)
  have hhiN : 4 * p ≤ 7 * 2 ^ k := by
    exact_mod_cast (by nlinarith : 4 * (p : ℝ) ≤ 7 * (2 : ℝ) ^ k)
  obtain ⟨hordinary, hkl⟩ := double_primitive (by omega : 3 ≤ k) hp hloN hhiN
  refine ⟨2 ^ k * p, ?_, Nat.mul_pos (by positivity) hp.pos, hordinary, hkl⟩
  have hlarge : k < 2 ^ k := Nat.lt_two_pow_self
  have hp1 := hp.one_le
  nlinarith

end D5.S3.Arith.Abundancy.ZelinskyZhangDoublePrimitive
