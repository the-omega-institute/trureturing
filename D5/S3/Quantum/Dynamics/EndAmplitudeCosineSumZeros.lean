/- GID: D5/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros
   generality: G
   mirror-B: D5/B/S3/Quantum/Dynamics/EndAmplitudeCosineSumZeros
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: For odd a < even b < odd c, gcd 1, the end numerator vanishes in (0, pi) iff a > 1. -/

/-
proof_shape: amplitudeNumerator_pos: content; escape_witness (form 1): the same-delivery
intermediate proposition D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt
(preregistered fact E1 of issue #14487), on the live path: for 1 < b < c with b even and c odd,
N(1, b, c; t) > 0 on [0, π). The reflection amplitudeNumerator_pi_sub writes
N(π - 2θ) = 2 B(θ), the substitution k² sin² θ - sin² kθ = (kθ)² (ψ θ - ψ (kθ)),
ψ x = (sin x / x)², gives
B = b² c² ((ψ θ - ψ (bθ)) ((cθ)² - θ²) - (ψ θ - ψ (cθ)) ((bθ)² - θ²)), and the sign is that
proposition at (θ, bθ, cθ). With it taken as given, the remaining steps are an instantiation and
normalisation.
proof_shape: exists_amplitudeNumerator_neg: content; escape_witness: the public conclusion itself
(form 2; preregistered fact E2 of issue #14487): for a ≥ 3 odd, a < b < c, b even, c odd,
gcd(a, b, c) = 1, a time in (0, π) with N < 0. If a ∤ b the time is π - 2πj/a for a residue j
chosen by the averaging argument of exists_index over Σ_{j<a} sin²(πjm/a) = a/2; if a ∣ b it is
π - 2πl/c with a l ≡ gcd(a, c) (mod c), and the sign is the estimate dvd_core from
sin y > y - y³/6 and sin x < x.
proof_shape: amplitudeNumerator_zero_iff: content; escape_witness (form 1): the two intermediate
propositions amplitudeNumerator_pos and exists_amplitudeNumerator_neg of this module, both on
the live path. The step added to them is an instantiation of Mathlib's intermediate value
theorem (intermediate_value_Ioo') with the continuity of N and N(0) > 0; taken alone, with the
two propositions as given, that step is bind-only.
Definition: amplitudeNumerator (public; the cosine sum N(a, b, c; t)).
Private helpers:
proof_shape: amplitudeNumerator_pi_sub: bind-only (Real.cos_nat_mul_pi_sub, Real.cos_two_mul
and ring normalisation); consumer: amplitudeNumerator_pos, exists_neg_of_not_dvd,
exists_neg_of_dvd.
proof_shape: amplitudeNumerator_zero_pos: bind-only (evaluation at 0); consumer:
amplitudeNumerator_zero_iff.
proof_shape: amplitudeNumerator_abs: bind-only (Real.cos_neg); consumer: exists_neg_of_index.
proof_shape: exists_neg_of_index: bind-only (evenness in t and interval bookkeeping); consumer:
exists_neg_of_not_dvd, exists_neg_of_dvd.
proof_shape: sin_pi_mul_div_ne_zero: bind-only (Real.sin_eq_zero_iff); consumer: exists_index.
proof_shape: sin_mul_eq_zero: bind-only (Real.sin_eq_zero_iff, Real.sin_int_mul_pi); consumer:
exists_index.
proof_shape: sum_sin_sq: bind-only (Real.sin_mul_sum_cos, Real.sin_sq_eq_half_sub); consumer:
exists_index.
proof_shape: exists_index: content (averaging over a full period of residues); consumer:
exists_neg_of_not_dvd.
proof_shape: exists_neg_of_not_dvd: content (escape witness as for
exists_amplitudeNumerator_neg, case a ∤ b); consumer: exists_amplitudeNumerator_neg.
proof_shape: sin_sq_add_nat_mul_pi: bind-only (Real.sin_add_nat_mul_pi); consumer:
exists_neg_of_dvd.
proof_shape: sin_sq_mul_lower: content (β² sin² x (1 - (βx)²/3) < sin² (βx) from
Real.sin_gt_sub_cube and Real.sin_sq_le_sq); consumer: dvd_core.
proof_shape: dvd_core: content (the real inequality of the case a ∣ b); consumer:
exists_neg_of_dvd.
proof_shape: exists_neg_of_dvd: content (escape witness as for exists_amplitudeNumerator_neg,
case a ∣ b); consumer: exists_amplitudeNumerator_neg.
admission_basis: escape-witness (issue #14487: the cosine-sum statement behind the seven-site
conjecture of arXiv:2507.18767, Library note D5/L/GraphInvariants/escobar2025earlystateexclusion).
The definition amplitudeNumerator is the bracket of Eq. (2.1) of that source at natural
frequencies. The source proves the triples (1, 2m, 2m + 1) (its Theorem 3.2: no zero in (0, π))
and (2m + 1, 2m + 2, 2m + 3) (its Theorem 3.4: exactly 2m zeros) and states the general case as a
conjecture; the statements for all admissible triples are derived here, and this module does not
state the conjecture itself.
Direct frozen dependencies: none (pinned Mathlib only). Same-delivery dependency:
  D5/S3/Quantum/Dynamics/SincSquareChordSlope.sincSq_chord_lt.
utility: none; no declaration is a bounded enumeration, checker, numeric reduction or certified
instance: every statement quantifies over all admissible integer triples and real times.
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Order.IntermediateValue
import D5.S3.Quantum.Dynamics.SincSquareChordSlope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros

open Real Finset

/-- Numerator of the first-site amplitude of a seven-site chain with spectrum `{0, ±a, ±b, ±c}`. -/
noncomputable def amplitudeNumerator (a b c : ℕ) (t : ℝ) : ℝ :=
  ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2)
    + (b : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2) * Real.cos (a * t)
    + (a : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * Real.cos (b * t)
    + (a : ℝ) ^ 2 * (b : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * Real.cos (c * t)

/-- Reflection about `π`: for `a`, `c` odd and `b` even the numerator at `π - 2 θ` is a
combination of squared sines. -/
private theorem amplitudeNumerator_pi_sub (a b c : ℕ) (ha : Odd a) (hb : Even b) (hc : Odd c)
    (θ : ℝ) :
    amplitudeNumerator a b c (π - 2 * θ) =
      2 * ((b : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (b : ℝ) ^ 2) * sin (a * θ) ^ 2
        - (a : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) * sin (b * θ) ^ 2
        + (a : ℝ) ^ 2 * (b : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) * sin (c * θ) ^ 2) := by
  have key : ∀ k : ℕ, cos (k * (π - 2 * θ)) = (-1) ^ k * (1 - 2 * sin (k * θ) ^ 2) := by
    intro k
    rw [mul_sub, cos_nat_mul_pi_sub, show (k : ℝ) * (2 * θ) = 2 * (k * θ) by ring, cos_two_mul,
      cos_sq']
    ring
  unfold amplitudeNumerator
  rw [key a, key b, key c, ha.neg_one_pow, hb.neg_one_pow, hc.neg_one_pow]
  ring

/-- The numerator is positive at time `0`. -/
private theorem amplitudeNumerator_zero_pos {a b c : ℕ} (ha : 0 < a) (hab : a < b)
    (hbc : b < c) : 0 < amplitudeNumerator a b c 0 := by
  have hA : (0 : ℝ) < a := by exact_mod_cast ha
  have hAB : (a : ℝ) < b := by exact_mod_cast hab
  have hBC : (b : ℝ) < c := by exact_mod_cast hbc
  have hB : (0 : ℝ) < b := hA.trans hAB
  have hC : (0 : ℝ) < c := hB.trans hBC
  have h1 : (0 : ℝ) < (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < (c : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) < (c : ℝ) ^ 2 - (b : ℝ) ^ 2 := by nlinarith
  have p0 := mul_pos (mul_pos h1 h2) h3
  have p1 := mul_pos (mul_pos (pow_pos hB 2) (pow_pos hC 2)) h3
  have p2 := mul_pos (mul_pos (pow_pos hA 2) (pow_pos hC 2)) h2
  have p3 := mul_pos (mul_pos (pow_pos hA 2) (pow_pos hB 2)) h1
  simp only [amplitudeNumerator, mul_zero, cos_zero, mul_one]
  linarith

/-- **Positivity for `a = 1`.** For `1 < b < c` with `b` even and `c` odd, the numerator with
smallest frequency `1` is positive on `[0, π)`. -/
theorem amplitudeNumerator_pos (b c : ℕ) (hb : Even b) (hc : Odd c) (h1 : 1 < b) (hbc : b < c)
    {t : ℝ} (ht0 : 0 ≤ t) (htπ : t < Real.pi) : 0 < amplitudeNumerator 1 b c t := by
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = (π - t) / 2 := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hθ2 : θ ≤ π / 2 := by rw [hθ]; linarith
  have ht : t = π - 2 * θ := by rw [hθ]; ring
  have hb1 : (1 : ℝ) < b := by exact_mod_cast h1
  have hbc' : (b : ℝ) < c := by exact_mod_cast hbc
  have hb0 : (0 : ℝ) < b := by linarith
  have hc0 : (0 : ℝ) < c := by linarith
  have hu : θ < b * θ := by nlinarith
  have huv : (b : ℝ) * θ < c * θ := by nlinarith
  have hchord := SincSquareChordSlope.sincSq_chord_lt hθ0 hθ2 hu huv
  have hθne : θ ≠ 0 := hθ0.ne'
  have hbne : (b : ℝ) ≠ 0 := hb0.ne'
  have hcne : (c : ℝ) ≠ 0 := hc0.ne'
  have e1 : sin θ ^ 2 = θ ^ 2 * (sin θ / θ) ^ 2 := by field_simp
  have e2 : sin (b * θ) ^ 2 = (b * θ) ^ 2 * (sin (b * θ) / (b * θ)) ^ 2 := by field_simp
  have e3 : sin (c * θ) ^ 2 = (c * θ) ^ 2 * (sin (c * θ) / (c * θ)) ^ 2 := by field_simp
  rw [ht, amplitudeNumerator_pi_sub 1 b c odd_one hb hc θ, Nat.cast_one, one_mul, e1, e2, e3]
  have hpos := mul_pos (mul_pos (pow_pos hb0 2) (pow_pos hc0 2)) (sub_pos.2 hchord)
  linarith

/-- The numerator is an even function of time. -/
private theorem amplitudeNumerator_abs (a b c : ℕ) (t : ℝ) :
    amplitudeNumerator a b c |t| = amplitudeNumerator a b c t := by
  rcases abs_choice t with h | h <;> rw [h]
  simp only [amplitudeNumerator, mul_neg, cos_neg]

/-- A negative value of the numerator at the reflected point `π - 2 π n / m`, with `m` odd and
`0 < n < m`, gives a negative value at a time in `(0, π)`. -/
private theorem exists_neg_of_index {a b c m n : ℕ} (hm : Odd m) (hn0 : 0 < n) (hnm : n < m)
    (hneg : amplitudeNumerator a b c (π - 2 * (π * n / m)) < 0) :
    ∃ t : ℝ, 0 < t ∧ t < π ∧ amplitudeNumerator a b c t < 0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnmR : (n : ℝ) < m := by exact_mod_cast hnm
  have hmR : (0 : ℝ) < m := hnR.trans hnmR
  have hθ0 : 0 < π * n / m := div_pos (mul_pos pi_pos hnR) hmR
  have hθπ : π * n / m < π := by
    rw [div_lt_iff₀ hmR]
    exact mul_lt_mul_of_pos_left hnmR pi_pos
  have hθ2 : π * n / m ≠ π / 2 := by
    intro h
    rw [div_eq_div_iff hmR.ne' two_ne_zero] at h
    have h2 : (n : ℝ) * 2 = m := mul_left_cancel₀ pi_ne_zero (by linarith)
    have h3 : n * 2 = m := by exact_mod_cast h2
    exact (Nat.not_even_iff_odd.2 hm) ⟨n, by omega⟩
  refine ⟨|π - 2 * (π * n / m)|, abs_pos.2 fun h => hθ2 (by linarith),
    abs_lt.2 ⟨by linarith, by linarith⟩, ?_⟩
  rw [amplitudeNumerator_abs]
  exact hneg

/-- `sin (π m / a)` does not vanish when `a` does not divide `m`. -/
private theorem sin_pi_mul_div_ne_zero {a m : ℕ} (ha : 0 < a) (hm : ¬ a ∣ m) :
    sin (π * m / a) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 h
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [eq_div_iff haR] at hn
  have h1 : (n : ℝ) * a = m := mul_left_cancel₀ pi_ne_zero (by linarith)
  have h2 : n * (a : ℤ) = (m : ℤ) := by exact_mod_cast h1
  exact hm (Int.natCast_dvd_natCast.1 (Dvd.intro_left n h2))

/-- If `sin (π m / a)` vanishes then so does every `sin (m (π j / a))`. -/
private theorem sin_mul_eq_zero {a m : ℕ} (h : sin (π * m / a) = 0) (j : ℕ) :
    sin (m * (π * j / a)) = 0 := by
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.1 h
  have e : (m : ℝ) * (π * j / a) = ((j * n : ℤ) : ℝ) * π := by
    push_cast
    linear_combination (-(j : ℝ)) * hn
  rw [e, sin_int_mul_pi]

/-- Over a full period of residues, the squared sines `sin² (π j m / a)` sum to `a / 2`. -/
private theorem sum_sin_sq {a m : ℕ} (ha : 0 < a) (hm : sin (π * m / a) ≠ 0) :
    ∑ j ∈ range a, sin (m * (π * j / a)) ^ 2 = a / 2 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hcos : ∑ j ∈ range a, cos (2 * π * m / a * j + 0) = 0 := by
    have h := sin_mul_sum_cos a (2 * π * m / a) 0
    rw [show (a : ℝ) * (2 * π * m / a) / 2 = m * π by field_simp, sin_nat_mul_pi, zero_mul,
      show 2 * π * (m : ℝ) / a / 2 = π * m / a by ring] at h
    exact (mul_eq_zero.1 h).resolve_left hm
  calc ∑ j ∈ range a, sin (m * (π * j / a)) ^ 2
      = ∑ j ∈ range a, (1 / 2 - cos (2 * π * m / a * j + 0) / 2) := by
        refine sum_congr rfl fun j _ => ?_
        rw [sin_sq_eq_half_sub,
          show 2 * ((m : ℝ) * (π * j / a)) = 2 * π * m / a * j + 0 by ring]
    _ = a / 2 := by
        rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, ← sum_div, hcos]
        ring

/-- If `a` does not divide `b`, some residue `0 < j < a` has
`0 < sin² (π j b / a)` and `sin² (π j c / a) ≤ sin² (π j b / a)`. -/
private theorem exists_index {a b : ℕ} (c : ℕ) (ha : 0 < a) (hab : ¬ a ∣ b) :
    ∃ j : ℕ, 0 < j ∧ j < a ∧ 0 < sin (b * (π * j / a)) ^ 2 ∧
      sin (c * (π * j / a)) ^ 2 ≤ sin (b * (π * j / a)) ^ 2 := by
  have hb := sin_pi_mul_div_ne_zero ha hab
  have ha1 : 1 < a := by
    rcases Nat.lt_or_ge 1 a with h | h
    · exact h
    · exact absurd (by rw [show a = 1 by omega]; exact one_dvd b) hab
  by_contra hcon
  push Not at hcon
  have hlt : ∑ j ∈ range a, sin (b * (π * j / a)) ^ 2 <
      ∑ j ∈ range a, sin (c * (π * j / a)) ^ 2 := by
    refine sum_lt_sum (fun j hj => ?_) ⟨1, mem_range.2 ha1, ?_⟩
    · rcases (sq_nonneg (sin (b * (π * j / a)))).eq_or_lt with h | h
      · rw [← h]
        exact sq_nonneg _
      · have hj0 : 0 < j := by
          rcases Nat.eq_zero_or_pos j with rfl | h0
          · simp at h
          · exact h0
        exact (hcon j hj0 (mem_range.1 hj) h).le
    · have e : (b : ℝ) * (π * (1 : ℕ) / a) = π * b / a := by
        push_cast
        ring
      have h1 : 0 < sin (b * (π * (1 : ℕ) / a)) ^ 2 := by
        rw [e]
        exact lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hb).symm
      exact hcon 1 one_pos ha1 h1
  rw [sum_sin_sq ha hb] at hlt
  have hle : ∑ j ∈ range a, sin (c * (π * j / a)) ^ 2 ≤ a / 2 := by
    by_cases h : sin (π * c / a) = 0
    · rw [sum_eq_zero fun j _ => by rw [sin_mul_eq_zero h j, zero_pow two_ne_zero]]
      positivity
    · exact (sum_sin_sq ha h).le
  linarith

/-- **A negative value when `a ∤ b`.** -/
private theorem exists_neg_of_not_dvd {a b c : ℕ} (ha : Odd a) (hb : Even b) (hc : Odd c)
    (hab : a < b) (hbc : b < c) (hdvd : ¬ a ∣ b) :
    ∃ t : ℝ, 0 < t ∧ t < π ∧ amplitudeNumerator a b c t < 0 := by
  obtain ⟨j, hj0, hja, hσb, hσ⟩ := exists_index c ha.pos hdvd
  refine exists_neg_of_index ha hj0 hja ?_
  have hA : (0 : ℝ) < a := by exact_mod_cast ha.pos
  have hAB : (a : ℝ) < b := by exact_mod_cast hab
  have hBC : (b : ℝ) < c := by exact_mod_cast hbc
  have hsin : sin (a * (π * j / a)) = 0 := by
    rw [show (a : ℝ) * (π * j / a) = j * π by field_simp]
    exact sin_nat_mul_pi j
  have h1 : (0 : ℝ) < (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  have h2 : (0 : ℝ) < (c : ℝ) ^ 2 - (b : ℝ) ^ 2 := by nlinarith
  have h3 : (0 : ℝ) < (c : ℝ) ^ 2 + (b : ℝ) ^ 2 - (a : ℝ) ^ 2 := by nlinarith
  have hC3 : (0 : ℝ) < (a : ℝ) ^ 2 * (b : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) :=
    mul_pos (mul_pos (pow_pos hA 2) (pow_pos (hA.trans hAB) 2)) h1
  have hC23 : (a : ℝ) ^ 2 * (b : ℝ) ^ 2 * ((b : ℝ) ^ 2 - (a : ℝ) ^ 2) <
      (a : ℝ) ^ 2 * (c : ℝ) ^ 2 * ((c : ℝ) ^ 2 - (a : ℝ) ^ 2) := by
    nlinarith [mul_pos (pow_pos hA 2) (mul_pos h2 h3)]
  rw [amplitudeNumerator_pi_sub a b c ha hb hc, hsin]
  linarith [mul_le_mul_of_nonneg_left hσ hC3.le, mul_lt_mul_of_pos_right hC23 hσb]

/-- Squared sines are invariant under shifts by integer multiples of `π`. -/
private theorem sin_sq_add_nat_mul_pi (x : ℝ) (n : ℕ) : sin (x + n * π) ^ 2 = sin x ^ 2 := by
  rcases neg_one_pow_eq_or ℝ n with h | h <;> rw [sin_add_nat_mul_pi, h] <;> ring

/-- For `0 < x` and `0 < β x < 4 / 3`, with `y = β x`:
`β² sin² x (1 - y² / 3) < sin² y`. -/
private theorem sin_sq_mul_lower {Bt x : ℝ} (hBt : 0 < Bt) (hx0 : 0 < x)
    (hy : Bt * x < 4 / 3) :
    Bt ^ 2 * sin x ^ 2 * (1 - (Bt * x) ^ 2 / 3) < sin (Bt * x) ^ 2 := by
  obtain ⟨y, hyd⟩ : ∃ y : ℝ, Bt * x = y := ⟨_, rfl⟩
  rw [hyd] at hy ⊢
  have hy0 : 0 < y := hyd ▸ mul_pos hBt hx0
  have hyy : y ^ 2 < 16 / 9 := by
    have h := mul_lt_mul'' hy hy hy0.le hy0.le
    linarith
  have hy2 : Bt ^ 2 * sin x ^ 2 ≤ y ^ 2 := by
    rw [← hyd, mul_pow]
    exact mul_le_mul_of_nonneg_left sin_sq_le_sq (sq_nonneg Bt)
  have h13 : 0 < 1 - y ^ 2 / 3 := by linarith
  have hS1 : 0 < y - y ^ 3 / 6 := by
    have h := mul_pos hy0 (by linarith : (0 : ℝ) < 1 - y ^ 2 / 6)
    linarith
  have hS2 : (y - y ^ 3 / 6) ^ 2 < sin y ^ 2 :=
    pow_lt_pow_left₀ (sin_gt_sub_cube hy0) hS1.le two_ne_zero
  have hS3 : y ^ 2 * (1 - y ^ 2 / 3) ≤ (y - y ^ 3 / 6) ^ 2 := by
    linarith [sq_nonneg (y ^ 3)]
  calc Bt ^ 2 * sin x ^ 2 * (1 - y ^ 2 / 3) ≤ y ^ 2 * (1 - y ^ 2 / 3) :=
        mul_le_mul_of_nonneg_right hy2 h13.le
    _ ≤ (y - y ^ 3 / 6) ^ 2 := hS3
    _ < sin y ^ 2 := hS2

/-- The real inequality behind the case `a ∣ b`: with `b = a β`, `β ≥ 2`, `3 d ≤ a`, `b < c`
and `x = π d / c`, one has `β² (c² - b²) sin² x < (c² - a²) sin² (β x)`. -/
private theorem dvd_core {A Bt C D x : ℝ} (hA : 0 < A) (hBt : 2 ≤ Bt) (hD : 0 < D)
    (hDA : 3 * D ≤ A) (hbc : A * Bt < C) (hx : C * x = π * D) :
    Bt ^ 2 * (C ^ 2 - (A * Bt) ^ 2) * sin x ^ 2 < (C ^ 2 - A ^ 2) * sin (Bt * x) ^ 2 := by
  have hBt0 : 0 < Bt := by linarith
  have hAC : A < C := by
    have h := mul_le_mul_of_nonneg_left hBt hA.le
    linarith
  have hC : 0 < C := hA.trans hAC
  have hx0 : 0 < x :=
    (pos_iff_pos_of_mul_pos (show 0 < C * x by rw [hx]; exact mul_pos pi_pos hD)).1 hC
  have hy3 : 3 * (Bt * x) < π := by
    have h1 : C * (3 * (Bt * x)) = π * (Bt * (3 * D)) := by linear_combination 3 * Bt * hx
    have h2 : Bt * (3 * D) < C :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left hDA hBt0.le) (by linarith)
    have h3 : C * (3 * (Bt * x)) < C * π := by
      rw [h1, mul_comm C π]
      exact mul_lt_mul_of_pos_left h2 pi_pos
    exact lt_of_mul_lt_mul_left h3 hC.le
  have hy43 : Bt * x < 4 / 3 := by linarith [pi_lt_four]
  have hsin := sin_sq_mul_lower hBt0 hx0 hy43
  have hK : 0 < C ^ 2 - A ^ 2 := by
    have h := mul_pos (sub_pos.2 hAC) (add_pos hC hA)
    linarith
  have hnum : (C ^ 2 - A ^ 2) * (Bt * x) ^ 2 / 3 ≤ A ^ 2 * (Bt ^ 2 - 1) := by
    have e : (C * (Bt * x)) ^ 2 = π ^ 2 * (Bt ^ 2 * D ^ 2) := by
      rw [show C * (Bt * x) = Bt * (C * x) by ring, hx]
      ring
    have hπ : π ^ 2 ≤ 4 ^ 2 := pow_le_pow_left₀ pi_pos.le pi_le_four 2
    have hD2 : D ^ 2 ≤ A ^ 2 / 9 := by
      have h := pow_le_pow_left₀ (mul_nonneg zero_le_three hD.le) hDA 2
      linarith
    have hBt2 : (2 : ℝ) ^ 2 ≤ Bt ^ 2 := pow_le_pow_left₀ zero_le_two hBt 2
    have h1 : π ^ 2 * (Bt ^ 2 * D ^ 2) ≤ 4 ^ 2 * (Bt ^ 2 * (A ^ 2 / 9)) :=
      mul_le_mul hπ (mul_le_mul_of_nonneg_left hD2 (sq_nonneg Bt)) (by positivity)
        (by norm_num)
    have h2 : 0 ≤ A ^ 2 * (Bt ^ 2 - 2 ^ 2) := mul_nonneg (sq_nonneg A) (by linarith)
    have h3 : 0 ≤ (A * (Bt * x)) ^ 2 := sq_nonneg _
    have h4 : (C ^ 2 - A ^ 2) * (Bt * x) ^ 2 = (C * (Bt * x)) ^ 2 - (A * (Bt * x)) ^ 2 := by
      ring
    rw [h4, e]
    linarith [sq_nonneg A]
  have hfin : 0 ≤ Bt ^ 2 * sin x ^ 2 *
      (A ^ 2 * (Bt ^ 2 - 1) - (C ^ 2 - A ^ 2) * (Bt * x) ^ 2 / 3) :=
    mul_nonneg (mul_nonneg (sq_nonneg Bt) (sq_nonneg (sin x))) (by linarith)
  linarith [mul_lt_mul_of_pos_left hsin hK, hfin]

/-- **A negative value when `a ∣ b`.** -/
private theorem exists_neg_of_dvd {a b c : ℕ} (ha : Odd a) (hb : Even b) (hc : Odd c)
    (hab : a < b) (hbc : b < c) (hdvd : a ∣ b) (hac : ¬ a ∣ c) :
    ∃ t : ℝ, 0 < t ∧ t < π ∧ amplitudeNumerator a b c t < 0 := by
  obtain ⟨β, rfl⟩ := hdvd
  have ha0 : 0 < a := ha.pos
  have hβ : 1 < β := lt_of_mul_lt_mul_left (by simpa using hab) (Nat.zero_le a)
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = Nat.gcd a c := ⟨_, rfl⟩
  have hd0 : 0 < d := hd ▸ Nat.gcd_pos_of_pos_left c ha0
  have hdc' : d ∣ c := hd ▸ Nat.gcd_dvd_right a c
  have hd3 : 3 * d ≤ a := by
    obtain ⟨e, he⟩ : d ∣ a := hd ▸ Nat.gcd_dvd_left a c
    have heodd : Odd e := Nat.Odd.of_mul_right (by rw [← he]; exact ha)
    have he1 : e ≠ 1 := by
      rintro rfl
      exact hac (by rw [he, mul_one]; exact hdc')
    obtain ⟨q, hq⟩ := heodd
    have he3 : 3 ≤ e := by omega
    have := Nat.mul_le_mul_left d he3
    linarith
  have hdc : Nat.gcd a c < c := by
    rw [← hd]
    have : a < c := lt_trans hab hbc
    omega
  obtain ⟨l, hlc, hl⟩ := Nat.exists_mul_mod_eq_gcd hdc
  rw [← hd] at hl
  have hl0 : 0 < l := by
    rcases Nat.eq_zero_or_pos l with rfl | h
    · simp at hl
      omega
    · exact h
  obtain ⟨k, hk⟩ : ∃ k : ℕ, a * l = c * k + d :=
    ⟨a * l / c, by rw [← hl]; exact (Nat.div_add_mod _ _).symm⟩
  refine exists_neg_of_index hc hl0 hlc ?_
  have hA : (0 : ℝ) < a := by exact_mod_cast ha0
  have hBt : (2 : ℝ) ≤ β := by exact_mod_cast hβ
  have hD : (0 : ℝ) < d := by exact_mod_cast hd0
  have hDA : 3 * (d : ℝ) ≤ a := by exact_mod_cast hd3
  have hBC : (a : ℝ) * β < c := by exact_mod_cast hbc
  have hC : (0 : ℝ) < c := lt_trans (mul_pos hA (by linarith)) hBC
  have hcne : (c : ℝ) ≠ 0 := hC.ne'
  have hkR : (a : ℝ) * l = c * k + d := by exact_mod_cast hk
  have hcore := dvd_core (x := π * d / c) hA hBt hD hDA hBC (by field_simp)
  have e_a : (a : ℝ) * (π * l / c) = π * d / c + k * π := by
    rw [show (a : ℝ) * (π * l / c) = π * ((a : ℝ) * l) / c by ring, hkR]
    field_simp
    ring
  have e_b : ((a * β : ℕ) : ℝ) * (π * l / c) = β * (π * d / c) + ((β * k : ℕ) : ℝ) * π := by
    push_cast
    rw [show (a : ℝ) * β * (π * l / c) = β * π * ((a : ℝ) * l) / c by ring, hkR]
    field_simp
    ring
  have h_a : sin (a * (π * l / c)) ^ 2 = sin (π * d / c) ^ 2 := by
    rw [e_a, sin_sq_add_nat_mul_pi]
  have h_b : sin (((a * β : ℕ) : ℝ) * (π * l / c)) ^ 2 = sin (β * (π * d / c)) ^ 2 := by
    rw [e_b, sin_sq_add_nat_mul_pi]
  have h_c : sin (c * (π * l / c)) = 0 := by
    rw [show (c : ℝ) * (π * l / c) = l * π by field_simp]
    exact sin_nat_mul_pi l
  rw [amplitudeNumerator_pi_sub a (a * β) c ha hb hc, h_a, h_b, h_c]
  push_cast
  linarith [mul_pos (mul_pos (pow_pos hA 2) (pow_pos hC 2)) (sub_pos.2 hcore)]

/-- **A negative value for `a ≥ 3`.** For `a < b < c` with `a`, `c` odd, `b` even,
`gcd (a, b, c) = 1` and `a ≥ 3`, the numerator is negative at some time in `(0, π)`. -/
theorem exists_amplitudeNumerator_neg (a b c : ℕ) (ha : Odd a) (hb : Even b) (hc : Odd c)
    (ha3 : 3 ≤ a) (hab : a < b) (hbc : b < c) (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ amplitudeNumerator a b c t < 0 := by
  by_cases hdvd : a ∣ b
  · refine exists_neg_of_dvd ha hb hc hab hbc hdvd fun hac => ?_
    have h1 : a ∣ 1 := hgcd ▸ Nat.dvd_gcd (Nat.dvd_gcd dvd_rfl hdvd) hac
    have := Nat.dvd_one.1 h1
    omega
  · exact exists_neg_of_not_dvd ha hb hc hab hbc hdvd

/-- **Zeros of the end amplitude numerator.** For `a < b < c` with `a`, `c` odd, `b` even and
`gcd (a, b, c) = 1`, the numerator vanishes somewhere in `(0, π)` if and only if `a ≠ 1`. -/
theorem amplitudeNumerator_zero_iff (a b c : ℕ) (ha : Odd a) (hb : Even b) (hc : Odd c)
    (hab : a < b) (hbc : b < c) (hgcd : Nat.gcd (Nat.gcd a b) c = 1) :
    (∃ t : ℝ, 0 < t ∧ t < Real.pi ∧ amplitudeNumerator a b c t = 0) ↔ a ≠ 1 := by
  constructor
  · rintro ⟨t, ht0, htπ, hz⟩ rfl
    exact (amplitudeNumerator_pos b c hb hc hab hbc ht0.le htπ).ne' hz
  · intro ha1
    have ha3 : 3 ≤ a := by
      obtain ⟨q, hq⟩ := ha
      omega
    obtain ⟨t₁, h0, hπ, hneg⟩ := exists_amplitudeNumerator_neg a b c ha hb hc ha3 hab hbc hgcd
    have hcont : Continuous (amplitudeNumerator a b c) := by
      unfold amplitudeNumerator
      fun_prop
    obtain ⟨t, ⟨ht0, htt₁⟩, hz⟩ := intermediate_value_Ioo' h0.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (amplitudeNumerator a b c t₁) (amplitudeNumerator a b c 0) from
        ⟨hneg, amplitudeNumerator_zero_pos ha.pos hab hbc⟩)
    exact ⟨t, ht0, htt₁.trans hπ, hz⟩

end D5.S3.Quantum.Dynamics.EndAmplitudeCosineSumZeros
