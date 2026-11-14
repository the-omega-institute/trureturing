/- GID: D5/S3/Arith/Divisors/DimitrovLowerBoundsC4C5
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovLowerBoundsC4C5
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dimitrov's full reciprocal-product Conjectures 4 and 5 are proved for all n ≥ 2 and k ≥ 1. -/

/-
admission_basis: open-problem-resolution (#30196; #30197; Proved)
escape_witness: none
proof_shape: every theorem below is bind-only after inlining all same-delivery helpers.
  h_mono: bind-only; consumer: ordered_reciprocal_bound.
  ordered_reciprocal_bound: bind-only; consumers: prove4, prove5.
  psi_ge: bind-only; consumers: prove4, prove5.
  sigma_ge_psi: bind-only; consumers: prove4, prove5.
  mixed_bound: bind-only; consumers: prove4, prove5.
  prove4: bind-only; consumer: result4.
  prove5: bind-only; consumer: result5.
  result4: bind-only; consumer: none; external endpoint: #30196.
  result5: bind-only; consumer: none; external endpoint: #30197.
claim4 and claim5 are source definitions consumed by result4 and result5 respectively.
The private auxiliaries are retained only as consumed proof organization, not as escape witnesses.
The source definitions and both claims preserve the complete original quantifier range and pointwise-power convention.
-/
import D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
import Mathlib.Tactic
set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

open ArithmeticFunction Finset
open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes

/-- Dimitrov Conjecture 4, with the source's full n ≥ 2 and k ≥ 1 quantifiers. -/
def claim4 : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) +
      (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ))) *
      (1 / ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))) +
       1 / ((psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))) +
       1 / ((ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ)))) ≥
      (5 * (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k +
        2 * ((n : ℝ) - 1) ^ (2 * k) +
        2 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2)) /
      ((n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k)

/-- Dimitrov Conjecture 5, with pointwise powers in every displayed occurrence. -/
def claim5 : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
      (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k)) *
      (1 / ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)) +
       1 / ((psi n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)) +
       1 / ((ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k))) ≥
      (10 * ((n : ℝ) - 1) ^ (2 * k) + 7 * ((n : ℝ) ^ 2 - 1) ^ k + ((n : ℝ) + 1) ^ (2 * k)) /
      (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k)

/-
MODIFIED APACHE-2.0 SOURCE PORT: the analytic supplier chain below is
FrontierMathLean.add_inv_mono_on_one → normalized_three_variable_inequality →
three_term_ratio_inequality, from pro20541/dimitrov-conjectures-lean at
95809b59deefd8dfad81e398250aedd7e1aea3b3, FrontierMathLean/AbstractInequality.lean
and FrontierMathLean/ThreeTermInequality.lean. Michael Mazur is the upstream
author/maintainer; upstream discloses substantive OpenAI Codex generation under
his direction. Modifications: local names/visibility, local-have packaging, and
one_div normalization. The complete license is docs/reports/licenses/dimitrov-LICENSE.txt;
immutable source URLs, hashes, mapping and receiver-pin retirement are in
Library/ArithUnits/dimitrov2026c4c5.md. No new mathematical content is claimed.
-/
/-- For positive `x` and `r`, if `1 ≤ r ≤ x`, then `x + x⁻¹ ≥ r + r⁻¹`.
The upstream parameters `r`, `x` are named `u`, `v` here. -/
private lemma h_mono {u v : ℝ} (hu : 1 ≤ u) (huv : u ≤ v) :
    u + 1 / u ≤ v + 1 / v := by
  simp only [one_div]
  have hr_pos : 0 < u := lt_of_lt_of_le zero_lt_one hu
  have hx_pos : 0 < v := lt_of_lt_of_le hr_pos huv
  have h₁ : 0 ≤ v - u := sub_nonneg.mpr huv
  have h₂ : 0 ≤ 1 - (v * u)⁻¹ := by
    rw [sub_nonneg]
    apply (inv_le_one₀ (mul_pos hx_pos hr_pos)).2
    have hx_one : 1 ≤ v := le_trans hu huv
    nlinarith [mul_nonneg (sub_nonneg.mpr hx_one) (sub_nonneg.mpr hu)]
  have hprod : 0 ≤ (v - u) * (1 - (v * u)⁻¹) := mul_nonneg h₁ h₂
  field_simp [hx_pos.ne', hr_pos.ne'] at hprod ⊢
  nlinarith

private lemma ordered_reciprocal_bound {X Y Z R : ℝ}
    (hX : 0 < X) (hXY : X ≤ Y) (hYZ : Y ≤ Z) (hR : 1 ≤ R)
    (hRle : R ≤ Y / X) :
    (X + Y + Z) * (1 / X + 1 / Y + 1 / Z) ≥ 5 + 2 * (R + 1 / R) := by
  -- The normalized three-variable inequality. Equality occurs at x = y = r.
  have normalized_three_variable_inequality
      {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
      5 + 2 * (r + r⁻¹) ≤
        3 + (x + x⁻¹) + (y + y⁻¹) + (x / y + y / x) := by
    have hx_pos : 0 < x := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hrx
    have hy_pos : 0 < y := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hr) hry
    have hx : r + r⁻¹ ≤ x + x⁻¹ := by simpa only [one_div] using h_mono hr hrx
    have hy : r + r⁻¹ ≤ y + y⁻¹ := by simpa only [one_div] using h_mono hr hry
    have hxy : 2 ≤ x / y + y / x := by
      have hsquare : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
      field_simp [hx_pos.ne', hy_pos.ne']
      nlinarith
    linarith
  -- If B/A and C/A are at least r ≥ 1, the sharp bound is attained at both ratios r.
  have three_term_ratio_inequality
      {A B C r : ℝ}
      (hA : 0 < A) (hB : 0 < B) (hC : 0 < C)
      (hr : 1 ≤ r) (hrB : r ≤ B / A) (hrC : r ≤ C / A) :
      5 + 2 * (r + r⁻¹) ≤
        (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
    have hnormalized := normalized_three_variable_inequality hr hrB hrC
    calc
      5 + 2 * (r + r⁻¹) ≤
          3 + (B / A + (B / A)⁻¹) + (C / A + (C / A)⁻¹) +
            ((B / A) / (C / A) + (C / A) / (B / A)) := hnormalized
      _ = (A + B + C) * (A⁻¹ + B⁻¹ + C⁻¹) := by
        field_simp [hA.ne', hB.ne', hC.ne']
        ring
  have hY : 0 < Y := lt_of_lt_of_le hX hXY
  have hZ : 0 < Z := lt_of_lt_of_le hY hYZ
  have hRZ : R ≤ Z / X := le_trans hRle (div_le_div_of_nonneg_right hYZ hX.le)
  simpa only [one_div] using (three_term_ratio_inequality hX hY hZ hR hRle hRZ)

private lemma psi_ge {n : ℕ} (hn : 2 ≤ n) : n + 1 ≤ psi n := by
  classical
  have hn0 : n ≠ 0 := by omega
  let p := n.minFac
  have hpprime : p.Prime := Nat.minFac_prime (by omega : n ≠ 1)
  have hpdiv : p ∣ n := Nat.minFac_dvd n
  have hpmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hpprime, hpdiv, hn0⟩
  have hsne : n.primeFactors.Nonempty := ⟨p, hpmem⟩
  have hle_erase :
      (∏ q ∈ n.primeFactors.erase p, q) ≤
        ∏ q ∈ n.primeFactors.erase p, (q + 1) := by
    apply Finset.prod_le_prod
    intro q hq
    omega
  have hpos_erase : 0 < ∏ q ∈ n.primeFactors.erase p, (q + 1) := by
    apply Finset.prod_pos
    intro q hq
    omega
  have hprod_lt : (∏ q ∈ n.primeFactors, q) < ∏ q ∈ n.primeFactors, (q + 1) := by
    rw [← Finset.mul_prod_erase n.primeFactors (fun q => q) hpmem,
      ← Finset.mul_prod_erase n.primeFactors (fun q => q + 1) hpmem]
    exact lt_of_le_of_lt (Nat.mul_le_mul_left p hle_erase)
      (Nat.mul_lt_mul_of_pos_right (by omega) hpos_erase)
  have hradpos : 0 < ∏ q ∈ n.primeFactors, q :=
    Finset.prod_pos (fun q hq => Nat.pos_of_mem_primeFactors hq)
  have hrad_dvd : (∏ q ∈ n.primeFactors, q) ∣ n := Nat.prod_primeFactors_dvd n
  have hquotpos : 0 < n / (∏ q ∈ n.primeFactors, q) :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hrad_dvd) hradpos
  have hmul_lt := Nat.mul_lt_mul_of_pos_left hprod_lt hquotpos
  have hmul : n / (∏ q ∈ n.primeFactors, q) * (∏ q ∈ n.primeFactors, q) = n :=
    Nat.div_mul_cancel hrad_dvd
  have hmul_lt' : n < (n / (∏ q ∈ n.primeFactors, q)) * (∏ q ∈ n.primeFactors, (q + 1)) := by
    calc
      n = n / (∏ q ∈ n.primeFactors, q) * (∏ q ∈ n.primeFactors, q) := hmul.symm
      _ < _ := hmul_lt
  change n + 1 ≤ (n / (∏ q ∈ n.primeFactors, q)) * (∏ q ∈ n.primeFactors, (q + 1))
  exact Nat.succ_le_of_lt hmul_lt'

private lemma sigma_ge_psi {n : ℕ} (hn : 2 ≤ n) : psi n ≤ ArithmeticFunction.sigma 1 n := by
  classical
  have hn0 : n ≠ 0 := by omega
  rw [psi_prod hn0, ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul (k := 1) hn0]
  apply Finset.prod_le_prod
  intro p hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have he : 1 ≤ n.factorization p := by
    exact hpp.factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
  rw [show n.factorization p + 1 = (n.factorization p - 1) + 1 + 1 by omega,
    Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [Nat.mul_one]
  rw [show p ^ (n.factorization p - 1 + 1) = p ^ (n.factorization p - 1) * p by rw [pow_succ]]
  have hsum_nonneg : 0 ≤ ∑ x ∈ range (n.factorization p - 1), p ^ x := by positivity
  have hpnonneg : 0 ≤ p ^ (n.factorization p - 1) := by positivity
  nlinarith [hpp.two_le]

private lemma mixed_bound {a b c q : ℝ} {m : ℕ}
    (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) (hm : 1 ≤ m)
    (hq : 1 ≤ q) (hql : q ≤ b / a) :
    let A := a ^ m * (b + c)
    let B := b ^ m * (a + c)
    let C := c ^ m * (a + b)
    A ≤ B ∧ B ≤ C ∧ q ^ (m - 1) * (1 + q) / 2 ≤ B / A := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hm' : m - 1 + 1 = m := by omega
  have hpa : a ^ (m - 1) ≤ b ^ (m - 1) :=
    pow_le_pow_left₀ (le_of_lt ha) hab (m - 1)
  have hpb : b ^ (m - 1) ≤ c ^ (m - 1) :=
    pow_le_pow_left₀ (le_of_lt hb) hbc (m - 1)
  have hpm_ab : a ^ m ≤ b ^ m := pow_le_pow_left₀ (le_of_lt ha) hab m
  have hpm_bc : b ^ m ≤ c ^ m := pow_le_pow_left₀ (le_of_lt hb) hbc m
  have hpow_a : a ^ m = a ^ (m - 1) * a := by
    calc
      a ^ m = a ^ (m - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]
  have hpow_b : b ^ m = b ^ (m - 1) * b := by
    calc
      b ^ m = b ^ (m - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]
  have hpow_c : c ^ m = c ^ (m - 1) * c := by
    calc
      c ^ m = c ^ (m - 1 + 1) := by congr 1 <;> omega
      _ = _ := by rw [pow_succ]
  let A := a ^ m * (b + c)
  let B := b ^ m * (a + c)
  let C := c ^ m * (a + b)
  have hA : 0 < A := by dsimp [A]; positivity
  have hBA : A ≤ B := by
    have h1 : 0 ≤ (b ^ m - a ^ m) * c :=
      mul_nonneg (sub_nonneg.mpr hpm_ab) (le_of_lt hc)
    have h2 : 0 ≤ a * b * (b ^ (m - 1) - a ^ (m - 1)) := by
      exact mul_nonneg (mul_nonneg (le_of_lt ha) (le_of_lt hb)) (sub_nonneg.mpr hpa)
    have hd : B - A = (b ^ m - a ^ m) * c + a * b * (b ^ (m - 1) - a ^ (m - 1)) := by
      dsimp [A, B]
      rw [hpow_a, hpow_b]
      ring
    nlinarith [h1, h2, hd]
  have hCB : B ≤ C := by
    have h1 : 0 ≤ (c ^ (m - 1) - b ^ (m - 1)) * (b * (a + c)) :=
      mul_nonneg (sub_nonneg.mpr hpb) (mul_nonneg (le_of_lt hb) (by positivity))
    have h2 : 0 ≤ c ^ (m - 1) * (a * (c - b)) :=
      mul_nonneg (le_of_lt (pow_pos hc _)) (mul_nonneg (le_of_lt ha) (sub_nonneg.mpr hbc))
    have hd : C - B = (c ^ (m - 1) - b ^ (m - 1)) * (b * (a + c)) +
        c ^ (m - 1) * (a * (c - b)) := by
      dsimp [B, C]
      rw [hpow_b, hpow_c]
      ring
    nlinarith [h1, h2, hd]
  have hqa : a * (1 + q) ≤ a + b := by
    have h := (le_div_iff₀ ha).mp hql
    nlinarith [h]
  have hpoly : (a + b) * (b + c) ≤ 2 * b * (a + c) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hab) (sub_nonneg.mpr hbc)]
  have hscale : b ^ (m - 1) * (a + b) * (b + c) ≤ 2 * b ^ m * (a + c) := by
    have h := mul_le_mul_of_nonneg_left hpoly (by positivity : 0 ≤ b ^ (m - 1))
    calc
      b ^ (m - 1) * (a + b) * (b + c) ≤ b ^ (m - 1) * (2 * b * (a + c)) := by
        nlinarith [h]
      _ = 2 * b ^ m * (a + c) := by rw [hpow_b]; ring
  have hqa0 : q * a ≤ b := by
    have h := (le_div_iff₀ ha).mp hql
    nlinarith [h]
  have hqpow : q ^ (m - 1) * a ^ (m - 1) ≤ b ^ (m - 1) := by
    have hpowqa : (q * a) ^ (m - 1) ≤ b ^ (m - 1) :=
      pow_le_pow_left₀ (mul_nonneg (le_trans (by norm_num) hq) (le_of_lt ha)) hqa0 _
    simpa [mul_pow] using hpowqa
  have hnum : q ^ (m - 1) * (1 + q) * A ≤ 2 * B := by
    calc
      q ^ (m - 1) * (1 + q) * A =
          q ^ (m - 1) * a ^ (m - 1) * (b + c) * (a * (1 + q)) := by
        dsimp [A]
        rw [hpow_a]
        ring
      _ ≤ q ^ (m - 1) * a ^ (m - 1) * (b + c) * (a + b) := by
        apply mul_le_mul_of_nonneg_left hqa (by positivity)
      _ = (q ^ (m - 1) * a ^ (m - 1)) * (a + b) * (b + c) := by ring
      _ ≤ b ^ (m - 1) * (a + b) * (b + c) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_right hqpow (by positivity)
        · positivity
      _ ≤ 2 * B := by
        dsimp [B]
        convert hscale using 1 <;> ring
  dsimp [A, B, C] at hBA hCB hA hnum ⊢
  refine ⟨hBA, hCB, ?_⟩
  apply (le_div_iff₀ hA).2
  nlinarith [hnum]



private theorem prove4 {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) +
      (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ)) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ))) *
      (1 / ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))) +
       1 / ((psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))) +
       1 / ((ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ)))) ≥
      (5 * (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k +
        2 * ((n : ℝ) - 1) ^ (2 * k) +
        2 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2)) /
      ((n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k) := by
  have hn0 : 0 < n := by omega
  have ha0 : 0 < (Nat.totient n : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hn0)
  have ha_le_nat : Nat.totient n + 1 ≤ n := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
  have ha_le : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have hcast : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast ha_le_nat
    linarith
  have hb_lower_nat : n + 1 ≤ psi n := psi_ge hn
  have hb_lower : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast hb_lower_nat
  have hb_sigma_nat : psi n ≤ ArithmeticFunction.sigma 1 n := sigma_ge_psi hn
  have hb_sigma : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by exact_mod_cast hb_sigma_nat
  have hb0 : 0 < (psi n : ℝ) := lt_of_lt_of_le (by positivity) hb_lower
  have hc0 : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := lt_of_lt_of_le hb0 hb_sigma
  have hnminus : 0 < (n : ℝ) - 1 := by
    have hcast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hq0 : 1 ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
    apply (le_div_iff₀ hnminus).2
    nlinarith
  have hqle0 : ((n : ℝ) + 1) / ((n : ℝ) - 1) ≤ (psi n : ℝ) / (Nat.totient n : ℝ) := by
    apply (div_le_div_iff₀ hnminus ha0).2
    nlinarith
  let q : ℝ := ((n : ℝ) + 1) / ((n : ℝ) - 1)
  let R : ℝ := (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) / ((n : ℝ) - 1) ^ k
  let A : ℝ := (Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let B : ℝ := (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ))
  have hmixed := mixed_bound (a := (Nat.totient n : ℝ)) (b := (psi n : ℝ))
      (c := (ArithmeticFunction.sigma 1 n : ℝ)) (q := q) (m := k)
      ha0 (by linarith) (by linarith) hk (by simpa [q] using hq0) (by simpa [q] using hqle0)
  have hA0 : 0 < A := by dsimp [A]; positivity
  have hReq : q ^ (k - 1) * (1 + q) / 2 = R := by
    dsimp [q, R]
    have hpow : ((n : ℝ) - 1) ^ k = ((n : ℝ) - 1) * ((n : ℝ) - 1) ^ (k - 1) := by
      calc
        ((n : ℝ) - 1) ^ k = ((n : ℝ) - 1) ^ ((k - 1) + 1) := by congr 1 <;> omega
        _ = _ := by rw [pow_succ]; ring
    rw [show 1 + ((n : ℝ) + 1) / ((n : ℝ) - 1) = 2 * (n : ℝ) / ((n : ℝ) - 1) by
      field_simp [hnminus.ne']
      ring]
    rw [div_pow]
    field_simp [hnminus.ne']
    rw [hpow]
  have hR0 : 1 ≤ R := by
    have hpowq : 1 ≤ q ^ (k - 1) := by
      simpa using (pow_le_pow_left₀ (a := (1 : ℝ)) (b := q) (by norm_num) (by simpa [q] using hq0) (k - 1))
    have hprod : 1 ≤ q ^ (k - 1) * ((1 + q) / 2) := by
      have hhalf : 1 ≤ (1 + q) / 2 := by linarith [hq0]
      have hnon : 0 ≤ (q ^ (k - 1) - 1) * ((1 + q) / 2 - 1) :=
        mul_nonneg (sub_nonneg.mpr hpowq) (sub_nonneg.mpr hhalf)
      nlinarith [hnon]
    rw [← hReq]
    simpa [div_eq_mul_inv, mul_assoc] using hprod
  have hordered := ordered_reciprocal_bound hA0 hmixed.1 hmixed.2.1 hR0 (by
    rw [← hReq]
    exact hmixed.2.2)
  calc
    _ = (A + B + C) * (1 / A + 1 / B + 1 / C) := by rfl
    _ ≥ 5 + 2 * (R + 1 / R) := hordered
    _ = _ := by
      dsimp [R]
      field_simp [hnminus.ne']
      rw [show 2 * k - 2 = (k - 1) * 2 by omega]
      ring


private theorem prove5 {n k : ℕ} (hn : 2 ≤ n) (hk : 1 ≤ k) :
    ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
      (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k) +
      (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k)) *
      (1 / ((Nat.totient n : ℝ) ^ k * ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)) +
       1 / ((psi n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)) +
       1 / ((ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k))) ≥
      (10 * ((n : ℝ) - 1) ^ (2 * k) + 7 * ((n : ℝ) ^ 2 - 1) ^ k + ((n : ℝ) + 1) ^ (2 * k)) /
      (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k) := by
  have hn0 : 0 < n := by omega
  have ha0 : 0 < (Nat.totient n : ℝ) := by exact_mod_cast (Nat.totient_pos.mpr hn0)
  have ha_le_nat : Nat.totient n + 1 ≤ n := Nat.succ_le_of_lt (Nat.totient_lt n (by omega))
  have ha_le : (Nat.totient n : ℝ) ≤ (n : ℝ) - 1 := by
    have hcast : (Nat.totient n : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast ha_le_nat
    linarith
  have hb_lower_nat : n + 1 ≤ psi n := psi_ge hn
  have hb_lower : (n : ℝ) + 1 ≤ (psi n : ℝ) := by exact_mod_cast hb_lower_nat
  have hb_sigma_nat : psi n ≤ ArithmeticFunction.sigma 1 n := sigma_ge_psi hn
  have hb_sigma : (psi n : ℝ) ≤ (ArithmeticFunction.sigma 1 n : ℝ) := by exact_mod_cast hb_sigma_nat
  have hb0 : 0 < (psi n : ℝ) := lt_of_lt_of_le (by positivity) hb_lower
  have hc0 : 0 < (ArithmeticFunction.sigma 1 n : ℝ) := lt_of_lt_of_le hb0 hb_sigma
  have hnminus : 0 < (n : ℝ) - 1 := by
    have hcast : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    linarith
  have hq0 : 1 ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
    apply (le_div_iff₀ hnminus).2
    nlinarith
  have hqle0 : ((n : ℝ) + 1) / ((n : ℝ) - 1) ≤ (psi n : ℝ) / (Nat.totient n : ℝ) := by
    apply (div_le_div_iff₀ hnminus ha0).2
    nlinarith
  let q : ℝ := (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ k
  let X : ℝ := ((n : ℝ) + 1) ^ k
  let Y : ℝ := ((n : ℝ) - 1) ^ k
  have hqXY : q = X / Y := by
    dsimp [q, X, Y]
    rw [div_pow]
  have hq : 1 ≤ q := by
    dsimp [q]
    simpa using (pow_le_pow_left₀ (a := (1 : ℝ)) (b := ((n : ℝ) + 1) / ((n : ℝ) - 1))
      (by norm_num) hq0 k)
  have hqle : q ≤ (psi n : ℝ) ^ k / (Nat.totient n : ℝ) ^ k := by
    dsimp [q]
    have h := pow_le_pow_left₀ (a := ((n : ℝ) + 1) / ((n : ℝ) - 1))
      (b := (psi n : ℝ) / (Nat.totient n : ℝ)) (by positivity) hqle0 k
    simpa [div_pow] using h
  let A : ℝ := (Nat.totient n : ℝ) ^ k * ((psi n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)
  let B : ℝ := (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (ArithmeticFunction.sigma 1 n : ℝ) ^ k)
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) ^ k + (psi n : ℝ) ^ k)
  have hmixed := mixed_bound (a := (Nat.totient n : ℝ) ^ k) (b := (psi n : ℝ) ^ k)
      (c := (ArithmeticFunction.sigma 1 n : ℝ) ^ k) (q := q) (m := 1)
      (by positivity) (by exact pow_le_pow_left₀ (le_of_lt ha0) (by linarith) k)
      (by exact pow_le_pow_left₀ (le_of_lt hb0) (by linarith) k) (by norm_num) hq hqle
  have hA0 : 0 < A := by dsimp [A]; positivity
  let R : ℝ := (1 + q) / 2
  have hR0 : 1 ≤ R := by
    dsimp [R]
    linarith
  have hAord : A ≤ B := by simpa [A, B] using hmixed.1
  have hBord : B ≤ C := by simpa [B, C] using hmixed.2.1
  have hRatio : R ≤ B / A := by
    dsimp [R]
    simpa [A, B] using hmixed.2.2
  have hordered := ordered_reciprocal_bound hA0 hAord hBord hR0 hRatio
  calc
    _ = (A + B + C) * (1 / A + 1 / B + 1 / C) := by rfl
    _ ≥ 5 + 2 * (R + 1 / R) := hordered
    _ = _ := by
      have hX : 0 < X := by dsimp [X]; positivity
      have hY : 0 < Y := by dsimp [Y]; exact pow_pos hnminus k
      have hplus : X + Y ≠ 0 := by positivity
      have hgeneric :
          5 + 2 * ((X / Y + 1) / 2 + 1 / ((X / Y + 1) / 2)) =
            (X ^ 2 + 7 * X * Y + 10 * Y ^ 2) / (Y * (X + Y)) := by
        field_simp [hY.ne', hplus]
        ring
      have htarget :
          5 + 2 * ((X / Y + 1) / 2 + 1 / ((X / Y + 1) / 2)) =
          (10 * ((n : ℝ) - 1) ^ (2 * k) + 7 * ((n : ℝ) ^ 2 - 1) ^ k + ((n : ℝ) + 1) ^ (2 * k)) /
          (((n : ℝ) - 1) ^ (2 * k) + ((n : ℝ) ^ 2 - 1) ^ k) := by
        rw [hgeneric]
        have hp : ((n : ℝ) ^ 2 - 1) ^ k = X * Y := by
          dsimp [X, Y]
          rw [show (n : ℝ) ^ 2 - 1 = ((n : ℝ) - 1) * ((n : ℝ) + 1) by ring, mul_pow]
          ring
        have hpow2 : ((n : ℝ) - 1) ^ (2 * k) = Y ^ 2 := by
          dsimp [Y]
          rw [show 2 * k = k + k by omega, pow_add]
          simp [pow_two]
        have hpow2x : ((n : ℝ) + 1) ^ (2 * k) = X ^ 2 := by
          dsimp [X]
          rw [show 2 * k = k + k by omega, pow_add]
          simp [pow_two]
        rw [hp, hpow2, hpow2x]
        ring
      dsimp [R]
      rw [hqXY]
      simpa [add_comm] using htarget


/-- The complete source Conjecture 4 is proved. -/
theorem result4 : claim4 := by
  intro n hn k hk
  exact prove4 hn hk

/-- The complete source Conjecture 5 is proved. -/
theorem result5 : claim5 := by
  intro n hn k hk
  exact prove5 hn hk

end D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5
