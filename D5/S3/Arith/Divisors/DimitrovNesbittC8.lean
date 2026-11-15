/- GID: D5/S3/Arith/Divisors/DimitrovNesbittC8
   generality: I
   mirror-B: D5/B/S3/Arith/Divisors/DimitrovNesbittC8
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: none
   digest: Dimitrov's complete mixed-power Nesbitt Conjecture 8 holds for every n ≥ 2 and k ≥ 1. -/

/-
admission_basis: open-problem-resolution (#30459; Proved)
escape_witness: none
proof_shape:
  balanced_pair_fraction_le: bind-only; consumer: normalized_nesbitt_ratio_inequality.
  nesbitt_envelope_mono: bind-only; consumer: normalized_nesbitt_ratio_inequality.
  normalized_nesbitt_ratio_inequality: bind-only; consumer: result.
  result: bind-only; consumer: none; full external endpoint: #30459.
The three auxiliaries are a consumed source port, not new mathematical content.
claim is the exact original source proposition consumed by result.
-/
import D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-! The complete mixed-power Nesbitt lower bound for Euler, Dedekind and divisor sums. -/

set_option autoImplicit false

namespace D5.S3.Arith.Divisors.DimitrovNesbittC8

open D5.S3.Arith.Divisors.OeisA344695GcdSigmaPsiPrimes
open D5.S3.Arith.Divisors.DimitrovLowerBoundsC4C5

/-- Conjecture 8 of arXiv:2606.12484v1, with all source quantifiers and unpowered inner sums. -/
def claim : Prop := ∀ n : ℕ, 2 ≤ n → ∀ k : ℕ, 1 ≤ k →
  let A : ℝ := (Nat.totient n : ℝ) ^ k * ((psi n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let B : ℝ := (psi n : ℝ) ^ k * ((Nat.totient n : ℝ) + (ArithmeticFunction.sigma 1 n : ℝ))
  let C : ℝ := (ArithmeticFunction.sigma 1 n : ℝ) ^ k * ((Nat.totient n : ℝ) + (psi n : ℝ))
  A / (B + C) + B / (A + C) + C / (A + B) ≥
    ((n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k +
      ((n : ℝ) - 1) ^ (2 * k) + 4 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2)) /
    (2 * (n : ℝ) ^ 2 * ((n : ℝ) + 1) ^ (2 * k - 2) +
      2 * (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) * ((n : ℝ) - 1) ^ k)

/-
MODIFIED APACHE-2.0 SOURCE PORT: balanced_pair_fraction_le,
nesbitt_envelope_mono and normalized_nesbitt_ratio_inequality are the consumed
cone from FrontierMathLean/NesbittRatioInequality.lean at
pro20541/dimitrov-conjectures-lean, 95809b59deefd8dfad81e398250aedd7e1aea3b3.
Michael Mazur is the upstream author/maintainer; upstream discloses substantive
OpenAI Codex generation under his direction. Modifications: namespace and private
visibility. Original source SHA-256:
49f2083f76f2a7fb8283d205c8921023e8dbe493482764841ab697b5b64903ca.
Full license: docs/reports/licenses/dimitrov-LICENSE.txt.
Mapping, immutable URLs and receiver-pin retirement: Library/ArithUnits/dimitrov2026c8.md.
-/
/-- Balancing two positive variables can only decrease the two asymmetric
fractions occurring in the normalized Nesbitt expression. -/
private lemma balanced_pair_fraction_le
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    2 * (x + y) / (x + y + 2) ≤ x / (1 + y) + y / (1 + x) := by
  have hxy2 : 0 < x + y + 2 := by linarith
  have h1x : 0 < 1 + x := by linarith
  have h1y : 0 < 1 + y := by linarith
  have hden : 0 < (1 + x) * (1 + y) * (x + y + 2) := by positivity
  have hid :
      x / (1 + y) + y / (1 + x) - 2 * (x + y) / (x + y + 2) =
        ((x + y + 1) * (x - y) ^ 2) /
          ((1 + x) * (1 + y) * (x + y + 2)) := by
    field_simp [h1x.ne', h1y.ne', hxy2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity


/-- The one-variable lower envelope is increasing from the point corresponding
to ratio one. -/
private lemma nesbitt_envelope_mono
    {s t : ℝ} (ht : 2 ≤ t) (hts : t ≤ s) :
    1 / t + 2 * t / (t + 2) ≤ 1 / s + 2 * s / (s + 2) := by
  have htpos : 0 < t := lt_of_lt_of_le (by norm_num) ht
  have hspos : 0 < s := lt_of_lt_of_le htpos hts
  have ht2 : 0 < t + 2 := by linarith
  have hs2 : 0 < s + 2 := by linarith
  have hfactor : 0 ≤ 3 * s * t - 2 * s - 2 * t - 4 := by
    have hst : 0 ≤ (s - 2) * (t - 2) :=
      mul_nonneg (sub_nonneg.mpr (ht.trans hts)) (sub_nonneg.mpr ht)
    nlinarith
  have hid :
      (1 / s + 2 * s / (s + 2)) - (1 / t + 2 * t / (t + 2)) =
        ((s - t) * (3 * s * t - 2 * s - 2 * t - 4)) /
          (s * t * (s + 2) * (t + 2)) := by
    field_simp [hspos.ne', htpos.ne', hs2.ne', ht2.ne']
    ring
  rw [← sub_nonneg, hid]
  positivity


/-- If `x` and `y` are both at least `r ≥ 1`, the normalized Nesbitt
expression has its sharp minimum at `x = y = r`. -/
private theorem normalized_nesbitt_ratio_inequality
    {x y r : ℝ} (hr : 1 ≤ r) (hrx : r ≤ x) (hry : r ≤ y) :
    (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) ≤
      1 / (x + y) + x / (1 + y) + y / (1 + x) := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hxpos : 0 < x := lt_of_lt_of_le hrpos hrx
  have hypos : 0 < y := lt_of_lt_of_le hrpos hry
  have htwor : 2 ≤ 2 * r := by linarith
  have hsum : 2 * r ≤ x + y := by linarith
  have hmono := nesbitt_envelope_mono htwor hsum
  have hbalance := balanced_pair_fraction_le hxpos hypos
  have hnormalized :
      (4 * r ^ 2 + r + 1) / (2 * (r ^ 2 + r)) =
        1 / (2 * r) + 2 * (2 * r) / (2 * r + 2) := by
    field_simp [hrpos.ne']
    ring
  rw [hnormalized]
  linarith

/-- The full original Dimitrov Conjecture 8 is proved. -/
theorem result : claim := by
  intro n hn k hk
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
  have hB0 : 0 < B := lt_of_lt_of_le hA0 hmixed.1
  have hC0 : 0 < C := lt_of_lt_of_le hB0 hmixed.2.1
  have hRB : R ≤ B / A := by rw [← hReq]; exact hmixed.2.2
  have hRC : R ≤ C / A :=
    hRB.trans (div_le_div_of_nonneg_right hmixed.2.1 hA0.le)
  have hnormalized := normalized_nesbitt_ratio_inequality hR0 hRB hRC
  have hAB : A + B ≠ 0 := (add_pos hA0 hB0).ne'
  have hAC : A + C ≠ 0 := (add_pos hA0 hC0).ne'
  have hBC : B + C ≠ 0 := (add_pos hB0 hC0).ne'
  calc
    _ = 1 / (B / A + C / A) + (B / A) / (1 + C / A) +
        (C / A) / (1 + B / A) := by
      change A / (B + C) + B / (A + C) + C / (A + B) = _
      field_simp [hA0.ne', hAB, hAC, hBC]
    _ ≥ (4 * R ^ 2 + R + 1) / (2 * (R ^ 2 + R)) := hnormalized
    _ = _ := by
      have hnreal : 0 < (n : ℝ) := by exact_mod_cast hn0
      have hnp : 0 < (n : ℝ) + 1 := by positivity
      have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR0
      have hsum : 0 < (n : ℝ) * ((n : ℝ) + 1) ^ (k - 1) + ((n : ℝ) - 1) ^ k :=
        add_pos (mul_pos hnreal (pow_pos hnp _)) (pow_pos hnminus _)
      dsimp [R]
      rw [show 2 * k - 2 = (k - 1) * 2 by omega]
      rw [show 2 * k = k * 2 by omega]
      simp only [pow_mul]
      field_simp [hnminus.ne', hnreal.ne', hnp.ne', hsum.ne']
      <;> ring

end D5.S3.Arith.Divisors.DimitrovNesbittC8
