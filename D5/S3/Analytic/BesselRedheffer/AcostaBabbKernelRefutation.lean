/- GID: D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation
   generality: I
   mirror-B: D5/B/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.claim; result=D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.result; claim=D5/S3/Analytic/BesselRedheffer/AcostaBabbKernelRefutation.claim
   digest: An exact two-mode counterexample to weighted Bessel-kernel positivity. -/

/-
proof_shape: result = bind-only; all private helper theorems = bind-only.
escape_witness: none.
admission_basis: open-problem-resolution (#22175; Refuted).
Direct frozen dependencies: F labels below are declaration statement_id values.
The public result is the designated refutation result (`basis=refutes`) and is exempt from
four-slot escape registration (CLAUDE.md §3.9).
The public definitions retain the source expressions; nbessel 0 is used directly.
The private term, term_nonneg, term_step, term_summable and term_eq_coeff of
D5.S3.Analytic.BesselRatioLogConcavity.Result are opened in place.
Their parameter is w = z ^ 2 / 4; 0 ≤ ν supplies -1 < ν. No duplicate term is defined.
The signed-series bridge also opens Series.entire and Series.nbessel_eq_entire in place.
The explicit weighted formula is the source object; its printed S formula is retained
without using the inconsistent printed Cesaro equality. The first two infima are
identified with isolated actual zeros. Only alpha=1/2, M=2, x=999/1000 is settled;
the uniform family, sharp threshold and downstream existence assertions remain open.

Frozen declaration identity key:
F1: D5/S3/Analytic/BesselRedheffer/Defs.firstZero
  sha256:0c735642b9a25c126b12da02f2aaa131b860d1af6ba85d3c9fbcc4558af14d65
F2: D5/S3/Analytic/BesselRedheffer/Defs.nbessel
  sha256:aa6d2843bd872d4dcd848de94567a652819fa03e4cf4b049a393984ff4495cf7
F3: D5/S3/Analytic/BesselRedheffer/Series.coeff
  sha256:8608141ffc114ca2c1e127301bae3bb0d2def8ce99965d20b40a7773f1deec2f
F4: D5/S3/Analytic/BesselRedheffer/Series.continuous_nbessel
  sha256:d429f33829e6b1752a51da05385377434a2c5514378a88344686ab9d73cca482
F5: D5/S3/Analytic/BesselRedheffer/Series.hasDerivAt_nbessel
  sha256:89484fd004b9cb9a5520ebb8f2d1442545bba4123e2a3158d1e18fd32b3d6f43
F6: D5/S3/Analytic/BesselRatioLogConcavity/Result.term
  sha256:925c234813959fd251b8579be2d1fff8150703f2c04c1b8e742aff8f350426a2
F7: D5/S3/Analytic/BesselRatioLogConcavity/Result.term_eq_coeff
  sha256:d64dc5ffb82d2cad46a0753a8e030b66b7bc3075ef76f49e01780525c97f9286
F8: D5/S3/Analytic/BesselRatioLogConcavity/Result.term_nonneg
  sha256:8f55227054b7eb4de3901196ffb28552346f265139fdd585e334e0a5d56287ff
F9: D5/S3/Analytic/BesselRatioLogConcavity/Result.term_step
  sha256:552b38c187d41603b76a898c5fbacbd63856dc0000ecfa9752bf6ebcf4dc4e75
F10: D5/S3/Analytic/BesselRatioLogConcavity/Result.term_summable
  sha256:c8db5cbd435bd48d7733b3cc7e5a7686de31dd799e73c117ba2297bcd6a0573e
F11: D5/S3/Analytic/BesselRedheffer/Series.entire
  sha256:0620ade8e8607860bb15ace6ff48c910bfd5125e7ead19865668788b8dc99e20
F12: D5/S3/Analytic/BesselRedheffer/Series.nbessel_eq_entire
  sha256:73b78ed59b670dbd7d181b9cf90ebd0701759e0b5c8f74803a291c5bc8fc91c6

Declaration rows: name | proof_shape | frozen dependencies | consumers | escape_witness.
All rows use the module admission basis above; definitions introduce the displayed objects.
j | bind-only | F1, F2 | K, S, point_negative, root_brackets, two_mode | none.
S | bind-only | F1, F2 | public source expression | none.
K | bind-only | F1, F2 | claim, point_negative, result, two_mode | none.
claim | bind-only | F1, F2 | result | none.
truncSum | bind-only | F6 | a_left_sign, a_right_sign, b_left_sign, b_right_sign, middle_negative, order_one_positive, partial_bounds, upper17 | none.
term_antitone | bind-only | F6, F8, F9 | partial_bounds | none.
nbessel_eq_signed | bind-only | F2, F3, F6, F7, F11, F12 | partial_bounds | none.
partial_bounds | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | bounds16, middle_negative, order_one_positive | none.
bounds16 | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | a_left_sign, a_right_sign, b_left_sign, b_right_sign, upper17 | none.
order_one_positive | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | first_decreasing | none.
upper | bind-only | F3 | order_one_negative, scaled_a_value, scaled_b_value, upper17 | none.
coeff_nonneg | bind-only | F3, F6, F7, F8 | partial_upper | none.
partial_upper | bind-only | F3, F6, F7, F8 | upper17 | none.
upper17 | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | order_one_negative, scaled_a_value, scaled_b_value | none.
a_left_sign | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | endpoint_signs | none.
a_right_sign | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | endpoint_signs | none.
b_left_sign | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | endpoint_signs | none.
b_right_sign | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | endpoint_signs | none.
endpoint_signs | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | root_brackets | none.
order_one_negative | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | second_increasing | none.
scaled_a_value | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | point_negative | none.
scaled_b_value | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | point_negative | none.
p10 | bind-only | none | central_identity, middle_negative | none.
centralCertificate | bind-only | none | central_identity, central_nonneg, middle_negative | none.
central_identity | bind-only | none | middle_negative | none.
central_nonneg | bind-only | none | middle_negative | none.
middle_negative | bind-only | F2, F3, F6, F7, F8, F9, F10, F11, F12 | root_brackets | none.
first_decreasing | bind-only | F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12 | root_brackets | none.
second_increasing | bind-only | F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12 | root_brackets | none.
root_brackets | bind-only | F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12 | point_negative | none.
two_mode | bind-only | F1, F2 | point_negative | none.
point_negative | bind-only | F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12 | result | none.
result | bind-only | F1, F2, F3, F4, F5, F6, F7, F8, F9, F10, F11, F12 | public settling result | none.
-/

import Batteries.Tactic.OpenPrivate
import D5.S3.Analytic.BesselRatioLogConcavity.Result
import D5.S3.Analytic.BesselRedheffer.Defs
import D5.S3.Analytic.BesselRedheffer.Series
import Mathlib.Tactic.NormNum.Parity



namespace D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation

open D5.S3.Analytic.BesselRedheffer.Defs

/- The source calls J_n the Bessel function of the first kind of order n,
   and j_m the m-th positive zero of J_0. The real owner nbessel 0 is
   Σ k, (-x²/4)^k/(k!)², the standard order-zero J series.
   No new J_0 definition or axiom is introduced here. -/

/-- The positive zeros in increasing order, indexed from one; index zero is unused. -/
noncomputable def j : ℕ → ℝ
  | 0 => 0
  | 1 => firstZero 0
  | n + 2 => sInf {x : ℝ | 0 < x ∧ j (n + 1) < x ∧ (nbessel 0) x = 0}

/-- Literal printed S_m^α, including j_m^α under the k-sum. This does not
imply the printed Cesàro equality and is not used to define K. -/
noncomputable def S (α : ℝ) (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 m, (j m) ^ α * (nbessel 0) (j k * x)

/-- The explicit weighted display, with the source's separate K_0^α ≡ 1. -/
noncomputable def K (α : ℝ) (M : ℕ) (x : ℝ) : ℝ :=
  if M = 0 then 1 else
    ∑ m ∈ Finset.Icc 1 M, (1 - (m : ℝ) / ((M : ℝ) + 1)) * (j m) ^ α * (nbessel 0) (j m * x)

/-- arXiv:2410.17681v1, Section 4, Conjecture 1, for the explicit weighted K. -/
def claim : Prop :=
  ∀ α : ℝ, 0 ≤ α → α ≤ (1 : ℝ) / 2 →
    ∀ M : ℕ, ∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 ≤ K α M x



open Filter Topology Finset
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 1600000


open private term term_nonneg term_step term_summable term_eq_coeff from
  D5.S3.Analytic.BesselRatioLogConcavity.Result

open private entire nbessel_eq_entire from D5.S3.Analytic.BesselRedheffer.Series

private noncomputable def truncSum (ν z : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, (-1 : ℝ) ^ n * term ν (z ^ 2 / 4) n

private theorem term_antitone {ν z : ℝ} {N : ℕ} (hν : 0 ≤ ν)
    (hsize : z ^ 2 / 4 ≤ (ν + 1 + N) * (N + 1)) :
    Antitone (fun n => term ν (z ^ 2 / 4) (n + N)) := by
  apply antitone_nat_of_succ_le
  intro n
  have hN : (N : ℝ) ≤ (n + N : ℕ) := by exact_mod_cast Nat.le_add_left N n
  have hden : 0 < ((n + N : ℕ) + 1 : ℝ) * (ν + 1 + (n + N : ℕ)) := by positivity
  have hsize' : z ^ 2 / 4 ≤ ((n + N : ℕ) + 1 : ℝ) * (ν + 1 + (n + N : ℕ)) := by
    calc
      _ ≤ (N + 1) * (ν + 1 + N) := by nlinarith [hsize]
      _ ≤ _ := mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  rw [show n + 1 + N = (n + N) + 1 by omega, term_step (by linarith : -1 < ν)]
  exact mul_le_of_le_one_left (term_nonneg (by linarith : -1 < ν) (by positivity : 0 ≤ z ^ 2 / 4) _) ((div_le_one hden).mpr hsize')

private theorem nbessel_eq_signed (ν z : ℝ) :
    nbessel ν z = ∑' n, (-1 : ℝ) ^ n * term ν (z ^ 2 / 4) n := by
  rw [nbessel_eq_entire]
  unfold entire
  apply tsum_congr
  intro n
  rw [term_eq_coeff]
  rw [show -(z ^ 2) / 4 = (-1 : ℝ) * (z ^ 2 / 4) by ring, mul_pow]
  ring

private theorem partial_bounds {ν z : ℝ} {N : ℕ} (hν : 0 ≤ ν)
    (hN : Even N) (hsize : z ^ 2 / 4 ≤ (ν + 1 + N) * (N + 1)) :
    truncSum ν z N ≤ nbessel ν z ∧ nbessel ν z ≤ truncSum ν z N + term ν (z ^ 2 / 4) N := by
  let f : ℕ → ℝ := fun n => term ν (z ^ 2 / 4) (n + N)
  have hfs : Summable f := (summable_nat_add_iff N).mpr (term_summable (by linarith : -1 < ν) (z ^ 2 / 4))
  have hfm : Antitone f := term_antitone hν hsize
  have hfl := hfs.tendsto_alternating_series_tsum
  have hlo := hfm.alternating_series_le_tendsto hfl 0
  have hhi := hfm.tendsto_le_alternating_series hfl 0
  simp only [mul_zero, sum_range_zero] at hlo
  simp only [mul_zero, zero_add, sum_range_one, pow_zero, one_mul] at hhi
  have he := ((term_summable (by linarith : -1 < ν) (z ^ 2 / 4)).alternating).sum_add_tsum_nat_add N
  have htail : (fun n => (-1 : ℝ) ^ (n + N) * term ν (z ^ 2 / 4) (n + N)) =
      (fun n => (-1 : ℝ) ^ n * f n) := by
    funext n
    rw [pow_add, hN.neg_one_pow, mul_one]
  rw [htail, ← nbessel_eq_signed ν z] at he
  change truncSum ν z N + (∑' n, (-1 : ℝ) ^ n * f n) = nbessel ν z at he
  have hhi' : (∑' n, (-1 : ℝ) ^ n * f n) ≤ term ν (z ^ 2 / 4) N := by
    simpa only [f, Nat.zero_add] using hhi
  constructor <;> linarith

private theorem bounds16 {ν z : ℝ} (hν : 0 ≤ ν) (hz : |z| ≤ 6) :
    truncSum ν z 16 ≤ nbessel ν z ∧ nbessel ν z ≤ truncSum ν z 16 + term ν (z ^ 2 / 4) 16 := by
  apply partial_bounds hν (by decide)
  have hz2 : z ^ 2 ≤ 36 := by nlinarith [sq_abs z, abs_nonneg z]
  have hp : (0 : ℝ) ≤ 17 * ν := by positivity
  norm_num
  nlinarith

private theorem order_one_positive {z : ℝ} (hz : |z| ≤ 481 / 200) : 0 < nbessel 1 z := by
  have hz2 : z ^ 2 ≤ (481 / 200 : ℝ) ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
  have hb := partial_bounds (ν := 1) (z := z) (N := 2) (by norm_num) (by decide)
    (by norm_num; nlinarith)
  have hpartial : truncSum 1 z 2 = 1 - z ^ 2 / 8 := by
    norm_num [truncSum, term, coeff, sum_range_succ, ascPochhammer_succ_eval]
    ring
  rw [hpartial] at hb
  nlinarith [hb.1]

private noncomputable def upper (ν lo hi : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ range N, coeff (ν + 1) n * (if Even n then hi ^ n else -(lo ^ n))

private theorem coeff_nonneg {ν : ℝ} (hν : 0 ≤ ν) (n : ℕ) :
    0 ≤ coeff (ν + 1) n := by
  have h := term_nonneg (ν := ν) (by linarith) (by norm_num : (0 : ℝ) ≤ 1) n
  simpa only [term_eq_coeff, one_pow, mul_one] using h

private theorem partial_upper {ν z lo hi : ℝ} (hν : 0 ≤ ν) (hlo : 0 ≤ lo)
    (hl : lo ≤ z ^ 2 / 4) (hu : z ^ 2 / 4 ≤ hi) (N : ℕ) :
    truncSum ν z N ≤ upper ν lo hi N := by
  apply sum_le_sum
  intro n hn
  simp_rw [term_eq_coeff]
  rcases Nat.even_or_odd n with he | ho
  · rw [ite_eq_left he, he.neg_one_pow, one_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu n) (coeff_nonneg hν n)
  · rw [ite_eq_right (Nat.not_even_iff_odd.mpr ho), ho.neg_one_pow, neg_one_mul]
    have hp := pow_le_pow_left₀ hlo hl n
    nlinarith [mul_nonneg (coeff_nonneg hν n) (sub_nonneg.mpr hp)]

private theorem upper17 {ν z lo hi : ℝ} (hν : 0 ≤ ν) (hz : |z| ≤ 6) (hlo : 0 ≤ lo)
    (hl : lo ≤ z ^ 2 / 4) (hu : z ^ 2 / 4 ≤ hi) : nbessel ν z ≤ upper ν lo hi 17 := by
  have hb := (bounds16 hν hz).2
  have he : truncSum ν z 16 + term ν (z ^ 2 / 4) 16 = truncSum ν z 17 := by
    norm_num [truncSum, sum_range_succ]
  rw [he] at hb
  exact hb.trans (partial_upper hν hlo hl hu 17)



open Finset
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 3200000
set_option maxRecDepth 2048

private theorem a_left_sign : 0 < nbessel 0 (24048255 / 10000000) := by
  have hb := (bounds16 (ν := 0) (z := 24048255 / 10000000) (by norm_num) (by norm_num)).1
  exact lt_of_lt_of_le (by norm_num [truncSum, term, coeff, sum_range_succ,
    ascPochhammer_succ_eval]) hb

private theorem a_right_sign : nbessel 0 (24048256 / 10000000) < 0 := by
  have hb := (bounds16 (ν := 0) (z := 24048256 / 10000000) (by norm_num) (by norm_num)).2
  exact lt_of_le_of_lt hb (by norm_num [truncSum, term, coeff, sum_range_succ,
    ascPochhammer_succ_eval])

private theorem b_left_sign : nbessel 0 (55200781 / 10000000) < 0 := by
  have hb := (bounds16 (ν := 0) (z := 55200781 / 10000000) (by norm_num) (by norm_num)).2
  exact lt_of_le_of_lt hb (by norm_num [truncSum, term, coeff, sum_range_succ,
    ascPochhammer_succ_eval])

private theorem b_right_sign : 0 < nbessel 0 (55200782 / 10000000) := by
  have hb := (bounds16 (ν := 0) (z := 55200782 / 10000000) (by norm_num) (by norm_num)).1
  exact lt_of_lt_of_le (by norm_num [truncSum, term, coeff, sum_range_succ,
    ascPochhammer_succ_eval]) hb

private theorem endpoint_signs :
    0 < nbessel 0 (24048255 / 10000000) ∧ nbessel 0 (24048256 / 10000000) < 0 ∧
    nbessel 0 (55200781 / 10000000) < 0 ∧ 0 < nbessel 0 (55200782 / 10000000) :=
  ⟨a_left_sign, a_right_sign, b_left_sign, b_right_sign⟩

private theorem order_one_negative {z : ℝ} (hzl : 138 / 25 ≤ z) (hzu : z ≤ 5521 / 1000) :
    nbessel 1 z < 0 := by
  have hz0 : 0 ≤ z := by linarith
  have hqlo : (138 / 25 : ℝ) ^ 2 / 4 ≤ z ^ 2 / 4 := by nlinarith
  have hqhi : z ^ 2 / 4 ≤ (5521 / 1000 : ℝ) ^ 2 / 4 := by nlinarith
  have hb := upper17 (ν := 1) (z := z) (by norm_num)
    (by rw [abs_of_nonneg hz0]; linarith)
    (by norm_num : (0 : ℝ) ≤ (138 / 25 : ℝ) ^ 2 / 4) hqlo hqhi
  exact lt_of_le_of_lt hb (by norm_num [upper, coeff, sum_range_succ,
    ascPochhammer_succ_eval])

private theorem scaled_a_value {a : ℝ} (hal : 24048255 / 10000000 ≤ a)
    (hau : a ≤ 24048256 / 10000000) : nbessel 0 (a * (999 / 1000)) ≤ 1 / 800 := by
  have ha0 : 0 ≤ a := by linarith
  have hz0 : 0 ≤ a * (999 / 1000 : ℝ) := by positivity
  have hzl : (24048255 / 10000000 : ℝ) * (999 / 1000) ≤ a * (999 / 1000) := by linarith
  have hzu : a * (999 / 1000) ≤ (24048256 / 10000000 : ℝ) * (999 / 1000) := by linarith
  have hqlo : ((24048255 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4 ≤
      (a * (999 / 1000)) ^ 2 / 4 := by nlinarith
  have hqhi : (a * (999 / 1000)) ^ 2 / 4 ≤
      ((24048256 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4 := by nlinarith
  have hb := upper17 (ν := 0) (z := a * (999 / 1000)) (by norm_num)
    (by rw [abs_of_nonneg hz0]; linarith)
    (by norm_num : (0 : ℝ) ≤ ((24048255 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4) hqlo hqhi
  exact hb.trans (by norm_num [upper, coeff, sum_range_succ, ascPochhammer_succ_eval])

private theorem scaled_b_value {b : ℝ} (hbl : 55200781 / 10000000 ≤ b)
    (hbu : b ≤ 55200782 / 10000000) : nbessel 0 (b * (999 / 1000)) ≤ -(187 / 100000) := by
  have hb0 : 0 ≤ b := by linarith
  have hz0 : 0 ≤ b * (999 / 1000 : ℝ) := by positivity
  have hzl : (55200781 / 10000000 : ℝ) * (999 / 1000) ≤ b * (999 / 1000) := by linarith
  have hzu : b * (999 / 1000) ≤ (55200782 / 10000000 : ℝ) * (999 / 1000) := by linarith
  have hqlo : ((55200781 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4 ≤
      (b * (999 / 1000)) ^ 2 / 4 := by nlinarith
  have hqhi : (b * (999 / 1000)) ^ 2 / 4 ≤
      ((55200782 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4 := by nlinarith
  have hb := upper17 (ν := 0) (z := b * (999 / 1000)) (by norm_num)
    (by rw [abs_of_nonneg hz0]; linarith)
    (by norm_num : (0 : ℝ) ≤ ((55200781 / 10000000 : ℝ) * (999 / 1000)) ^ 2 / 4) hqlo hqhi
  exact hb.trans (by norm_num [upper, coeff, sum_range_succ, ascPochhammer_succ_eval])



open Finset
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096

private noncomputable def p10 (q : ℝ) : ℝ :=
  ∑ n ∈ range 11, (-1 : ℝ) ^ n * q ^ n / ((n.factorial : ℝ) ^ 2)

private noncomputable def centralCertificate (u : ℝ) : ℝ :=
    (185137341166614376574821313582341298156147795908885199284673 / 2298186889847164108800000000000000000000000000000000000000000000 : ℝ) * u ^ 0 * (1 - u) ^ 10 +
    (3076044726911528959814342839779457701383877991709891157928801 / 1154223326374133760000000000000000000000000000000000000000000 : ℝ) * u ^ 1 * (1 - u) ^ 9 +
    (176011105967173068332102910551534908414978776488329502433 / 9620726743040000000000000000000000000000000000000000000 : ℝ) * u ^ 2 * (1 - u) ^ 8 +
    (6964906118535456578923049537358141581852474172769282447 / 126835752960000000000000000000000000000000000000000000 : ℝ) * u ^ 3 * (1 - u) ^ 7 +
    (79926542948746483386124545229023388800560606780826491 / 849346560000000000000000000000000000000000000000000 : ℝ) * u ^ 4 * (1 - u) ^ 6 +
    (92790935568593667218951705773991438344366211501047 / 921600000000000000000000000000000000000000000000 : ℝ) * u ^ 5 * (1 - u) ^ 5 +
    (33052339019338572792466724610271601003871773233 / 480000000000000000000000000000000000000000000 : ℝ) * u ^ 6 * (1 - u) ^ 4 +
    (289317324414301073197789483799963136112216549 / 9843750000000000000000000000000000000000000 : ℝ) * u ^ 7 * (1 - u) ^ 3 +
    (34945029020085281105488480368682290580519 / 4882812500000000000000000000000000000000 : ℝ) * u ^ 8 * (1 - u) ^ 2 +
    (50804507282635617912981660563584305287 / 66757202148437500000000000000000000000 : ℝ) * u ^ 9 * (1 - u) ^ 1 +
    (35444051062331358141362980569337 / 2607703208923339843750000000000000000 : ℝ) * u ^ 10 * (1 - u) ^ 0

private theorem central_identity (u : ℝ) :
    -(p10 ((231361 / 160000 : ℝ) + ((4761 / 625 : ℝ) - (231361 / 160000 : ℝ)) * u) + 1 / 100000) =
      centralCertificate u := by
  norm_num [p10, sum_range_succ, centralCertificate]
  ring

private theorem central_nonneg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ centralCertificate u := by
  unfold centralCertificate
  positivity

private theorem middle_negative {z : ℝ} (hzl : 481 / 200 ≤ z) (hzu : z ≤ 138 / 25) :
    nbessel 0 z < 0 := by
  have hz0 : 0 ≤ z := by linarith
  have hlo : (231361 / 160000 : ℝ) ≤ z ^ 2 / 4 := by norm_num; nlinarith
  have hhi : z ^ 2 / 4 ≤ (4761 / 625 : ℝ) := by norm_num; nlinarith
  let u := (z ^ 2 / 4 - (231361 / 160000 : ℝ)) / ((4761 / 625 : ℝ) - (231361 / 160000 : ℝ))
  have hu0 : 0 ≤ u := by dsimp [u]; exact div_nonneg (sub_nonneg.mpr hlo) (by norm_num)
  have hu1 : u ≤ 1 := by dsimp [u]; rw [div_le_one (by norm_num)]; linarith
  have he : (231361 / 160000 : ℝ) + ((4761 / 625 : ℝ) - (231361 / 160000 : ℝ)) * u = z ^ 2 / 4 := by
    dsimp [u]
    ring
  have hid := central_identity u
  rw [he] at hid
  have hp := central_nonneg hu0 hu1
  have hb := (partial_bounds (ν := 0) (z := z) (N := 10) (by norm_num) (by decide)
    (by norm_num; nlinarith)).2
  have hpoly : truncSum 0 z 10 + term 0 (z ^ 2 / 4) 10 = p10 (z ^ 2 / 4) := by
    norm_num [truncSum, term, coeff, p10, sum_range_succ, ascPochhammer_succ_eval]
    ring
  rw [hpoly] at hb
  linarith



open Set
open D5.S3.Analytic.BesselRedheffer.Defs
open D5.S3.Analytic.BesselRedheffer.Series

set_option maxHeartbeats 1600000

private theorem first_decreasing : StrictAntiOn (nbessel 0) (Icc 0 (481 / 200)) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc _ _) (continuous_nbessel (by norm_num)).continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [(hasDerivAt_nbessel (ν := 0) (by norm_num) z).deriv]
  have hp := order_one_positive (z := z) (by rw [abs_of_pos hz.1]; exact hz.2.le)
  norm_num
  nlinarith [mul_pos hz.1 hp]

private theorem second_increasing : StrictMonoOn (nbessel 0) (Icc (138 / 25) (5521 / 1000)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_nbessel (by norm_num)).continuousOn
  intro z hz
  rw [interior_Icc] at hz
  rw [(hasDerivAt_nbessel (ν := 0) (by norm_num) z).deriv]
  have hn := order_one_negative hz.1.le hz.2.le
  have hz0 : 0 < z := by linarith [hz.1]
  norm_num
  nlinarith [mul_neg_of_pos_of_neg hz0 hn]

private theorem root_brackets :
    (24048255 / 10000000 ≤ D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 1 ∧
      D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 1 ≤ 24048256 / 10000000) ∧
    (55200781 / 10000000 ≤ D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 2 ∧
      D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 2 ≤ 55200782 / 10000000) := by
  obtain ⟨hasign, hatop, hbsign, hbtop⟩ := endpoint_signs
  obtain ⟨a, ha, hza⟩ := intermediate_value_Icc'
    (by norm_num : (24048255 / 10000000 : ℝ) ≤ 24048256 / 10000000)
    (continuous_nbessel (ν := 0) (by norm_num)).continuousOn ⟨hatop.le, hasign.le⟩
  obtain ⟨b, hb, hzb⟩ := intermediate_value_Icc
    (by norm_num : (55200781 / 10000000 : ℝ) ≤ 55200782 / 10000000)
    (continuous_nbessel (ν := 0) (by norm_num)).continuousOn ⟨hbsign.le, hbtop.le⟩
  have ha0 : 0 < a := by linarith [ha.1]
  have hb0 : 0 < b := by linarith [hb.1]
  have hab : a < b := by linarith [ha.2, hb.1]
  have haIn : a ∈ Set.Icc 0 (481 / 200) := ⟨ha0.le, by linarith [ha.2]⟩
  have hbIn : b ∈ Set.Icc (138 / 25) (5521 / 1000) := ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hfirst : firstZero 0 = a := by
    unfold firstZero
    apply le_antisymm
    · have hbelow : BddBelow {x : ℝ | 0 < x ∧ nbessel 0 x = 0} :=
        ⟨0, fun x hx => hx.1.le⟩
      exact csInf_le hbelow ⟨ha0, hza⟩
    · have hne : ({x : ℝ | 0 < x ∧ nbessel 0 x = 0} : Set ℝ).Nonempty :=
        ⟨a, ha0, hza⟩
      apply le_csInf hne
      rintro r ⟨hr, hzr⟩
      by_contra hn
      have hra : r < a := lt_of_not_ge hn
      have hm := first_decreasing ⟨hr.le, hra.le.trans haIn.2⟩ haIn hra
      rw [hzr, hza] at hm
      exact (lt_irrefl 0) hm
  have hj1 : D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 1 = a := by
    exact Real.ext_cauchy (congrArg Real.cauchy hfirst)
  have hnob : ∀ r : ℝ, 0 < r → a < r → nbessel 0 r = 0 → b ≤ r := by
    intro r hr har hzr
    by_contra hn
    have hrb : r < b := lt_of_not_ge hn
    have hneg : nbessel 0 r < 0 := by
      by_cases hsmall : r ≤ 481 / 200
      · have hm := first_decreasing haIn ⟨hr.le, hsmall⟩ har
        simpa only [hza] using hm
      · by_cases hmid : r ≤ 138 / 25
        · exact middle_negative (lt_of_not_ge hsmall).le hmid
        · have hm := second_increasing
            ⟨(lt_of_not_ge hmid).le, hrb.le.trans hbIn.2⟩ hbIn hrb
          simpa only [hzb] using hm
    rw [hzr] at hneg
    exact (lt_irrefl 0) hneg
  have hj2 : D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 2 = b := by
    change sInf {x : ℝ | 0 < x ∧ D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation.j 1 < x ∧ nbessel 0 x = 0} = b
    rw [hj1]
    apply le_antisymm
    · have hbelow : BddBelow {x : ℝ | 0 < x ∧ a < x ∧ nbessel 0 x = 0} :=
        ⟨0, fun x hx => hx.1.le⟩
      exact csInf_le hbelow ⟨hb0, hab, hzb⟩
    · have hne : ({x : ℝ | 0 < x ∧ a < x ∧ nbessel 0 x = 0} : Set ℝ).Nonempty :=
        ⟨b, hb0, hab, hzb⟩
      exact le_csInf hne (fun r hr => hnob r hr.1 hr.2.1 hr.2.2)
  rw [hj1, hj2]
  exact ⟨ha, hb⟩



open D5.S3.Analytic.BesselRedheffer.Defs

set_option maxHeartbeats 1600000

private theorem two_mode (α x : ℝ) :
    K α 2 x = (2 * (j 1) ^ α * nbessel 0 (j 1 * x) +
      (j 2) ^ α * nbessel 0 (j 2 * x)) / 3 := by
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by exact Finset.val_inj.mp rfl
  norm_num [K, hIcc]
  ring

private theorem point_negative : K (1 / 2) 2 (999 / 1000) < 0 := by
  obtain ⟨ha, hb⟩ := root_brackets
  have ha0 : 0 ≤ j 1 := by linarith [ha.1]
  have hb0 : 0 ≤ j 2 := by linarith [hb.1]
  have hsqra := Real.sq_sqrt ha0
  have hsqrb := Real.sq_sqrt hb0
  have hsa0 := Real.sqrt_nonneg (j 1)
  have hsb0 := Real.sqrt_nonneg (j 2)
  have hsa : Real.sqrt (j 1) ≤ 1551 / 1000 := by nlinarith [ha.2]
  have hsb : 2349 / 1000 ≤ Real.sqrt (j 2) := by nlinarith [hb.1]
  have hfa := scaled_a_value ha.1 ha.2
  have hfb := scaled_b_value hb.1 hb.2
  have hmulA : Real.sqrt (j 1) * nbessel 0 (j 1 * (999 / 1000)) ≤
      (1551 / 1000) * (1 / 800) := by
    calc
      _ ≤ Real.sqrt (j 1) * (1 / 800) := mul_le_mul_of_nonneg_left hfa hsa0
      _ ≤ _ := mul_le_mul_of_nonneg_right hsa (by norm_num)
  have hmulB : Real.sqrt (j 2) * nbessel 0 (j 2 * (999 / 1000)) ≤
      (2349 / 1000) * (-(187 / 100000)) := by
    calc
      _ ≤ Real.sqrt (j 2) * (-(187 / 100000)) := mul_le_mul_of_nonneg_left hfb hsb0
      _ ≤ _ := mul_le_mul_of_nonpos_right hsb (by norm_num)
  rw [two_mode, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  nlinarith

theorem result : ¬ claim := by
  intro h
  have hp := h (1 / 2) (by norm_num) (by norm_num) 2 (999 / 1000) (by norm_num) (by norm_num)
  exact (not_le_of_gt point_negative) hp

end D5.S3.Analytic.BesselRedheffer.AcostaBabbKernelRefutation
