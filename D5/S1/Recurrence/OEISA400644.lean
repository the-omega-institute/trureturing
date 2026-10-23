/- GID: D5/S1/Recurrence/OEISA400644
   generality: I
   mirror-B: D5/B/S1/Recurrence/OEISA400644
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The exact rounded three-term norm sequence has the Tribonacci square-root ratio limit. -/

import Mathlib
import D5.S0.Tower.Tribonacci.Values
import D5.S0.Tower.Tribonacci.PerronRoot
import D5.S1.Recurrence.ComplementaryGoldenRatioLimit

namespace D5.S1.Recurrence.OEISA400644

open Filter

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Tower.Tribonacci.Values
open D5.S0.Tower.Tribonacci.PerronRoot

noncomputable def rho : ℝ := Real.sqrt tribonacciConstant

theorem rho_pos : 0 < rho := by
  unfold rho
  exact Real.sqrt_pos.2 tribonacciConstant_pos

theorem rho_sextic : rho ^ 6 - rho ^ 4 - rho ^ 2 - 1 = 0 := by
  have hs : rho ^ 2 = tribonacciConstant := by
    unfold rho
    exact Real.sq_sqrt tribonacciConstant_pos.le
  rw [show rho ^ 6 = (rho ^ 2) ^ 3 by ring,
    show rho ^ 4 = (rho ^ 2) ^ 2 by ring, hs]
  nlinarith [tribonacciConstant_cubic]

theorem positive_sextic_root_eq_rho {x : ℝ} (hx : 0 < x)
    (hxpoly : x ^ 6 - x ^ 4 - x ^ 2 - 1 = 0) : x = rho := by
  let t : ℝ := x ^ 2
  have htpos : 0 < t := by positivity
  have htcubic : t ^ 3 = t ^ 2 + t + 1 := by
    dsimp [t]
    nlinarith
  have ht_one : 1 < t := by
    by_contra h
    have hle : t ≤ 1 := le_of_not_gt h
    nlinarith [sq_nonneg (t - 1)]
  have ht_eq : t = tribonacciConstant :=
    eq_tribonacciConstant_of_one_lt ht_one htcubic
  have hs : rho ^ 2 = tribonacciConstant := by
    unfold rho
    exact Real.sq_sqrt tribonacciConstant_pos.le
  have hsq : x ^ 2 = rho ^ 2 := by
    dsimp [t] at ht_eq
    nlinarith
  exact (sq_eq_sq₀ hx.le rho_pos.le).mp hsq

theorem rho_is_largest_positive_root :
    0 < rho ∧ rho ^ 6 - rho ^ 4 - rho ^ 2 - 1 = 0 ∧
      ∀ x : ℝ, 0 < x → x ^ 6 - x ^ 4 - x ^ 2 - 1 = 0 → x ≤ rho := by
  refine ⟨rho_pos, rho_sextic, ?_⟩
  intro x hx hroot
  exact (positive_sextic_root_eq_rho hx hroot).le

/-- The integer nearest-square operation used by the OEIS Python source.
For an integer radicand `s`, `Nat.sqrt s` is the lower candidate and the
threshold selects the upper candidate. -/
def sourceRound (s : ℕ) : ℕ :=
  let r := Nat.sqrt s
  r + if s > r * r + r then 1 else 0

/-- The sequence with the source's three initial values and recurrence.
The zero-based presentation is `a 0 = a 1 = 0`, `a 2 = 1`; source index `n`
is represented by `a (n - 1)` for `n ≥ 1`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | n + 3 => sourceRound (a (n + 2) ^ 2 + a (n + 1) ^ 2 + a n ^ 2)

/-- The lower and upper integer-square brackets around every radicand. -/
theorem sqrt_bracket (s : ℕ) :
    Nat.sqrt s * Nat.sqrt s ≤ s ∧
      s < (Nat.sqrt s + 1) * (Nat.sqrt s + 1) := by
  constructor
  · exact Nat.sqrt_le s
  · simpa [Nat.succ_eq_add_one] using Nat.lt_succ_sqrt s

/-- The source integer threshold has exactly the two nearest candidates. -/
theorem sourceRound_spec (s : ℕ) :
    let r := Nat.sqrt s
    r * r ≤ s ∧ s < (r + 1) * (r + 1) ∧
      (sourceRound s = r ∨ sourceRound s = r + 1) := by
  dsimp [sourceRound]
  have hb := sqrt_bracket s
  by_cases h : s > Nat.sqrt s * Nat.sqrt s + Nat.sqrt s
  · exact ⟨hb.1, hb.2, Or.inr (by simp [h])⟩
  · exact ⟨hb.1, hb.2, Or.inl (by simp [h])⟩

/-- The source step never falls below the lower square-root candidate. -/
theorem sourceRound_ge_sqrt (s : ℕ) : Nat.sqrt s ≤ sourceRound s := by
  dsimp [sourceRound]
  by_cases h : s > Nat.sqrt s * Nat.sqrt s + Nat.sqrt s <;> simp [h]

/- The integer domain has no half-integer square roots, so the source
threshold is a strict nearest-integer rounding rule over every reachable
radicand. -/
theorem sourceRound_real_error (s : ℕ) :
    |Real.sqrt (s : ℝ) - (sourceRound s : ℝ)| < (1 : ℝ) / 2 := by
  let r : ℕ := Nat.sqrt s
  have hb := sourceRound_spec s
  have hsquare : (Real.sqrt (s : ℝ)) ^ 2 = (s : ℝ) := by
    exact Real.sq_sqrt (by positivity)
  have hlow : (r : ℝ) ^ 2 ≤ (s : ℝ) := by
    have h := hb.1
    have hcast : (Nat.sqrt s : ℝ) * Nat.sqrt s ≤ (s : ℝ) := by
      exact_mod_cast h
    simpa [r, pow_two] using hcast
  have hupp : (s : ℝ) < ((r : ℝ) + 1) ^ 2 := by
    have h := hb.2.1
    have hcast : (s : ℝ) < ((Nat.sqrt s : ℝ) + 1) * ((Nat.sqrt s : ℝ) + 1) := by
      exact_mod_cast h
    simpa [r, pow_two] using hcast
  have hrnonneg : (0 : ℝ) ≤ r := by positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt (s : ℝ) := Real.sqrt_nonneg _
  by_cases h : s > r * r + r
  · have hone : r * r + r + 1 ≤ s := by omega
    have honeR : (r : ℝ) ^ 2 + r + 1 ≤ (s : ℝ) := by
      simpa [pow_two] using (show ((r * r + r + 1 : ℕ) : ℝ) ≤ (s : ℝ) by
        exact_mod_cast hone)
    have hroot_lo : (r : ℝ) + (1 : ℝ) / 2 < Real.sqrt (s : ℝ) := by
      nlinarith
    have hroot_hi : Real.sqrt (s : ℝ) < (r : ℝ) + 1 + (1 : ℝ) / 2 := by
      nlinarith
    have hround : sourceRound s = r + 1 := by simp [sourceRound, r, h]
    have hroundR : (sourceRound s : ℝ) = (r : ℝ) + 1 := by
      rw [hround]
      norm_num
    rw [hroundR]
    rw [abs_lt]
    constructor <;> nlinarith
  · have hle : s ≤ r * r + r := by omega
    have hleR : (s : ℝ) ≤ (r : ℝ) ^ 2 + r := by
      simpa [pow_two] using (show (s : ℝ) ≤ ((r * r + r : ℕ) : ℝ) by
        exact_mod_cast hle)
    have hroot_lo : (r : ℝ) - (1 : ℝ) / 2 < Real.sqrt (s : ℝ) := by
      nlinarith
    have hroot_hi : Real.sqrt (s : ℝ) < (r : ℝ) + (1 : ℝ) / 2 := by
      nlinarith
    have hround : sourceRound s = r := by simp [sourceRound, r, h]
    have hroundR : (sourceRound s : ℝ) = (r : ℝ) := by rw [hround]
    rw [hroundR]
    rw [abs_lt]
    constructor <;> nlinarith

/-- Exact initial values in the zero-based presentation. -/
theorem a_zero : a 0 = 0 := rfl

theorem a_one : a 1 = 0 := rfl

theorem a_two : a 2 = 1 := rfl

/-- Exact recurrence, with no reindexing or approximation. -/
theorem a_recurrence (n : ℕ) :
    a (n + 3) = sourceRound (a (n + 2) ^ 2 + a (n + 1) ^ 2 + a n ^ 2) := by
  rfl

theorem a_mono (n : ℕ) : a n ≤ a (n + 1) := by
  rcases n with (_ | _ | n)
  · simp [a]
  · simp [a]
  · rw [a_recurrence n]
    calc
      a (n + 2) ≤ Nat.sqrt
          (a (n + 2) ^ 2 + a (n + 1) ^ 2 + a n ^ 2) := by
        apply (Nat.le_sqrt).2
        simpa [pow_two, Nat.add_assoc] using
          (Nat.le_add_right (a (n + 2) ^ 2)
            (a (n + 1) ^ 2 + a n ^ 2))
      _ ≤ sourceRound
          (a (n + 2) ^ 2 + a (n + 1) ^ 2 + a n ^ 2) :=
        sourceRound_ge_sqrt _

theorem a_pos (n : ℕ) : 1 ≤ a (n + 2) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
      exact le_trans ih (a_mono (n + 2))

/-- The recursive construction is unique among natural-valued sequences with
these initial values and this exact source step. -/
theorem a_unique {b : ℕ → ℕ}
    (h0 : b 0 = 0) (h1 : b 1 = 0) (h2 : b 2 = 1)
    (hrec : ∀ n : ℕ,
      b (n + 3) = sourceRound (b (n + 2) ^ 2 + b (n + 1) ^ 2 + b n ^ 2)) :
    ∀ n : ℕ, b n = a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with (_ | _ | _ | n)
      · simpa [a] using h0
      · simpa [a] using h1
      · simpa [a] using h2
      · rw [hrec n, a]
        rw [ih (n + 2) (by omega), ih (n + 1) (by omega), ih n (by omega)]

private theorem a_le {i j : ℕ} (h : i ≤ j) : a i ≤ a j :=
  (monotone_nat_of_le_succ a_mono) h

private theorem a_block_growth (n : ℕ) : a (n + 2) + 1 ≤ a (n + 5) := by
  let s := a (n + 4) ^ 2 + a (n + 3) ^ 2 + a (n + 2) ^ 2
  have hp : (1 : ℝ) ≤ a (n + 2) := by exact_mod_cast a_pos n
  have h1 : (a (n + 2) : ℝ) ≤ a (n + 3) := by exact_mod_cast a_le (by omega : n+2 ≤ n+3)
  have h2 : (a (n + 2) : ℝ) ≤ a (n + 4) := by exact_mod_cast a_le (by omega : n+2 ≤ n+4)
  have hs : (s : ℝ) = (a (n+4) : ℝ)^2 + (a (n+3) : ℝ)^2 + (a (n+2) : ℝ)^2 := by
    simp [s]
  have herr := (abs_lt.mp (sourceRound_real_error s)).2
  have hrec : a (n+5) = sourceRound s := a_recurrence (n+2)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ s by positivity)
  have hroot := Real.sqrt_nonneg (s : ℝ)
  have hlt : (a (n+2) : ℝ) < a (n+5) := by
    rw [hrec]
    nlinarith [sq_nonneg ((a (n+3) : ℝ) - a (n+2)),
      sq_nonneg ((a (n+4) : ℝ) - a (n+2))]
  have : a (n+2) < a (n+5) := by exact_mod_cast hlt
  omega

private theorem a_block_lower (n : ℕ) : n+1 ≤ a (3*n+2) := by
  induction n with
  | zero => simp [a]
  | succ n ih =>
    have hg := a_block_growth (3*n)
    rw [show 3*(n+1)+2 = 3*n+5 by omega]
    omega

private theorem a_tendsto : Tendsto (fun n => (a (n+2) : ℝ)) atTop atTop := by
  have hnat : Tendsto (fun n => a (n+2)) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop (3*k)] with n hn
    exact le_trans (by omega : k ≤ k+1)
      (le_trans (a_block_lower k) (a_le (by omega)))
  exact tendsto_natCast_atTop_atTop.comp hnat

private noncomputable def b (n : ℕ) : ℝ := (a (n+2) : ℝ)^2
private noncomputable def err (n : ℕ) : ℝ := b (n+3) - b (n+2) - b (n+1) - b n
private noncomputable def proj (n : ℕ) : ℝ :=
  b (n+2) + (tribonacciConstant-1)*b (n+1) + tribonacciConstant⁻¹*b n

private theorem b_pos (n : ℕ) : 0 < b n := by
  have hp : (0 : ℝ) < a (n+2) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (a_pos n))
  exact sq_pos_of_pos hp

private theorem proj_ge (n : ℕ) : b (n+2) ≤ proj n := by
  dsimp [proj]
  have ht := one_lt_tribonacciConstant
  have hb0 := b_pos n
  have hb1 := b_pos (n+1)
  have hti := inv_pos.mpr tribonacciConstant_pos
  nlinarith

private theorem proj_pos (n : ℕ) : 0 < proj n := lt_of_lt_of_le (b_pos _) (proj_ge n)

private theorem err_bound (n : ℕ) : |err n| ≤ 2 * (a (n+4) : ℝ) := by
  let s := a (n+4)^2+a (n+3)^2+a (n+2)^2
  have hrec : a (n+5) = sourceRound s := a_recurrence (n+2)
  have herr := abs_lt.mp (sourceRound_real_error s)
  have hs : (s : ℝ) = (a (n+4) : ℝ)^2+(a (n+3) : ℝ)^2+(a (n+2) : ℝ)^2 := by simp [s]
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ s by positivity)
  have hroot := Real.sqrt_nonneg (s : ℝ)
  have hp : (1 : ℝ) ≤ a (n+4) := by exact_mod_cast a_pos (n+2)
  have h1 : (a (n+2) : ℝ) ≤ a (n+4) := by exact_mod_cast a_le (by omega : n+2 ≤ n+4)
  have h2 : (a (n+3) : ℝ) ≤ a (n+4) := by exact_mod_cast a_le (by omega : n+3 ≤ n+4)
  have hrootbound : Real.sqrt (s : ℝ) < 7/4 * (a (n+4) : ℝ) := by
    nlinarith [sq_nonneg ((a (n+4) : ℝ) - a (n+2)),
      sq_nonneg ((a (n+4) : ℝ) - a (n+3))]
  have hrecast : (a (n+5) : ℝ) = sourceRound s := by exact_mod_cast hrec
  dsimp [err, b]
  rw [abs_le]
  simp only [Nat.add_assoc, Nat.reduceAdd] at *
  constructor <;> nlinarith [sq_nonneg ((sourceRound s : ℝ) - Real.sqrt (s : ℝ))]

private theorem proj_step (n : ℕ) : proj (n+1) = tribonacciConstant * proj n + err n := by
  have ht := tribonacciConstant_cubic
  have hne := tribonacciConstant_ne_zero
  dsimp [proj, err]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  have hid : tribonacciConstant*(tribonacciConstant-1) = 1+tribonacciConstant⁻¹ := by
    field_simp
    nlinarith
  have hmul := mul_inv_cancel₀ hne
  linear_combination -b (n+1)*hid - b n*hmul

private theorem relative_err_bound (n : ℕ) :
    |err n / proj n| ≤ 2 / (a (n+4) : ℝ) := by
  have hp : (0 : ℝ) < a (n+4) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (a_pos (n+2)))
  rw [abs_div, abs_of_pos (proj_pos n)]
  calc
    |err n| / proj n ≤ (2 * (a (n+4) : ℝ)) / proj n :=
      div_le_div_of_nonneg_right (err_bound n) (proj_pos n).le
    _ ≤ (2 * (a (n+4) : ℝ)) / (a (n+4) : ℝ)^2 := by
      apply div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hp)
      simpa [b] using proj_ge n
    _ = 2 / (a (n+4) : ℝ) := by field_simp <;> ring

private theorem relative_err_tendsto :
    Tendsto (fun n => err n / proj n) atTop (nhds 0) := by
  have hgrowth : Tendsto (fun n => (a (n+4) : ℝ)) atTop atTop := by
    simpa [Nat.add_assoc] using (tendsto_add_atTop_iff_nat 2).2 a_tendsto
  have hbound : Tendsto (fun n => 2 / (a (n+4) : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hgrowth
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using relative_err_bound n) hbound

private theorem proj_ratio_tendsto :
    Tendsto (fun n => proj (n+1) / proj n) atTop (nhds tribonacciConstant) := by
  have heq (n : ℕ) : proj (n+1) / proj n = tribonacciConstant + err n / proj n := by
    rw [proj_step]
    field_simp [(proj_pos n).ne']
  simp_rw [heq]
  simpa using tendsto_const_nhds.add relative_err_tendsto


private noncomputable def v (n : ℕ) : ℝ := b (n+2) / proj n
private noncomputable def ca (n : ℕ) : ℝ :=
  (tribonacciConstant-1) * (proj (n+1) / proj (n+2))
private noncomputable def cb (n : ℕ) : ℝ :=
  tribonacciConstant⁻¹ * (proj n / proj (n+1)) * (proj (n+1) / proj (n+2))
private noncomputable def alpha : ℝ := (tribonacciConstant-1) / tribonacciConstant
private noncomputable def beta : ℝ := tribonacciConstant⁻¹ ^ 3
private noncomputable def center : ℝ := 1 / (1+alpha+beta)

private theorem v_bounds (n : ℕ) : 0 ≤ v n ∧ v n ≤ 1 := by
  constructor
  · exact div_nonneg (b_pos _).le (proj_pos _).le
  · exact (div_le_one (proj_pos _)).2 (proj_ge n)

private theorem v_step (n : ℕ) :
    v (n+2) = 1 - ca n * v (n+1) - cb n * v n := by
  dsimp [v, ca, cb]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  field_simp [(proj_pos n).ne', (proj_pos (n+1)).ne', (proj_pos (n+2)).ne']
  dsimp [proj]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  ring

private theorem ca_limit : Tendsto ca atTop (nhds alpha) := by
  change Tendsto (fun n => (tribonacciConstant-1) * (proj (n+1) / proj (n+2))) atTop (nhds alpha)
  have hi : Tendsto (fun n => proj n / proj (n+1)) atTop (nhds tribonacciConstant⁻¹) := by
    simpa only [inv_div] using proj_ratio_tendsto.inv₀ tribonacciConstant_ne_zero
  have hi1 := (tendsto_add_atTop_iff_nat 1).2 hi
  simpa [ca, alpha, div_eq_mul_inv, Nat.add_assoc] using
    hi1.const_mul (tribonacciConstant-1)

private theorem cb_limit : Tendsto cb atTop (nhds beta) := by
  change Tendsto (fun n => tribonacciConstant⁻¹ * (proj n / proj (n+1)) *
    (proj (n+1) / proj (n+2))) atTop (nhds beta)
  have hi : Tendsto (fun n => proj n / proj (n+1)) atTop (nhds tribonacciConstant⁻¹) := by
    simpa only [inv_div] using proj_ratio_tendsto.inv₀ tribonacciConstant_ne_zero
  have hi1 := (tendsto_add_atTop_iff_nat 1).2 hi
  convert (hi.const_mul tribonacciConstant⁻¹).mul hi1 using 1 <;>
    simp [beta, pow_succ, Nat.add_assoc]

private theorem coefficient_bounds : 0 ≤ alpha ∧ 0 ≤ beta ∧ alpha+beta < 1 := by
  have ht := one_lt_tribonacciConstant
  have htp := tribonacciConstant_pos
  have hti := inv_pos.mpr htp
  have hq : alpha+beta < 1 := by
    dsimp [alpha, beta]
    rw [show (tribonacciConstant-1)/tribonacciConstant + tribonacciConstant⁻¹^3 =
      ((tribonacciConstant-1)*tribonacciConstant^2+1)/tribonacciConstant^3 by
        field_simp <;> ring]
    apply (div_lt_one (pow_pos htp 3)).2
    nlinarith [sq_pos_of_pos (sub_pos.mpr ht)]
  exact ⟨div_nonneg (by linarith) htp.le, pow_nonneg hti.le _, hq⟩

private theorem center_pos : 0 < center := by
  dsimp [center]
  have h := coefficient_bounds
  exact one_div_pos.mpr (by linarith [h.1, h.2.1])

private noncomputable def delta (n : ℕ) : ℝ := v n - center
private noncomputable def forcing (n : ℕ) : ℝ :=
  (alpha-ca n)*v (n+1) + (beta-cb n)*v n

private theorem forcing_bound (n : ℕ) : |forcing n| ≤ |alpha-ca n| + |beta-cb n| := by
  dsimp [forcing]
  calc
    _ ≤ |(alpha-ca n)*v (n+1)| + |(beta-cb n)*v n| := abs_add_le _ _
    _ = |alpha-ca n| * v (n+1) + |beta-cb n| * v n := by
      rw [abs_mul, abs_mul, abs_of_nonneg (v_bounds (n+1)).1, abs_of_nonneg (v_bounds n).1]
    _ ≤ _ := by nlinarith [(v_bounds (n+1)).2, (v_bounds n).2, abs_nonneg (alpha-ca n), abs_nonneg (beta-cb n)]

private theorem forcing_limit : Tendsto forcing atTop (nhds 0) := by
  have ha : Tendsto (fun n => |alpha-ca n|) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => alpha) atTop (nhds alpha)).sub ca_limit).abs
  have hb : Tendsto (fun n => |beta-cb n|) atTop (nhds 0) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => beta) atTop (nhds beta)).sub cb_limit).abs
  exact squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using forcing_bound n)
    (by simpa using ha.add hb)

private theorem delta_step (n : ℕ) :
    delta (n+2) = forcing n - alpha*delta (n+1) - beta*delta n := by
  have hc : (1+alpha+beta)*center = 1 := by
    dsimp [center]
    have h := coefficient_bounds
    have hden : 1+alpha+beta ≠ 0 := by linarith [h.1,h.2.1]
    field_simp [hden]
  dsimp [delta, forcing]
  rw [v_step]
  nlinarith

private theorem delta_limit : Tendsto delta atTop (nhds 0) := by
  let q := alpha+beta
  let m : ℕ → ℝ := fun n => max |delta (2*n)| |delta (2*n+1)|
  let f : ℕ → ℝ := fun n => (1+alpha) * (|forcing (2*n)| + |forcing (2*n+1)|)
  have hcoef := coefficient_bounds
  have hq0 : 0 ≤ q := add_nonneg hcoef.1 hcoef.2.1
  have hq1 : q < 1 := hcoef.2.2
  have hn : Tendsto (fun n : ℕ => 2*n) atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with n hn
    omega
  have hn1 : Tendsto (fun n : ℕ => 2*n+1) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right _ _) hn
  have hf : Tendsto f atTop (nhds 0) := by
    dsimp [f]
    simpa using ((forcing_limit.comp hn).abs.add (forcing_limit.comp hn1).abs).const_mul (1+alpha)
  have hstep (n : ℕ) : m (n+1) ≤ q*m n + |f n| := by
    have h0 : |delta (2*n)| ≤ m n := le_max_left _ _
    have h1 : |delta (2*n+1)| ≤ m n := le_max_right _ _
    have h2 : |delta (2*n+2)| ≤ q*m n + |forcing (2*n)| := by
      rw [delta_step]
      calc
        _ ≤ |forcing (2*n)| + |alpha*delta (2*n+1)| + |beta*delta (2*n)| := by
          simpa [sub_eq_add_neg, add_assoc] using
            (abs_add_three (forcing (2*n)) (-(alpha*delta (2*n+1))) (-(beta*delta (2*n))))
        _ = |forcing (2*n)| + alpha*|delta (2*n+1)| + beta*|delta (2*n)| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hcoef.1, abs_of_nonneg hcoef.2.1]
        _ ≤ _ := by dsimp [q]; nlinarith
    have h3 : |delta (2*n+3)| ≤ q*m n + alpha*|forcing (2*n)| + |forcing (2*n+1)| := by
      have hs := delta_step (2*n+1)
      simp only [Nat.add_assoc, Nat.reduceAdd] at hs
      rw [hs]
      have htriangle : |forcing (2*n+1) - alpha*delta (2*n+2) - beta*delta (2*n+1)| ≤
          |forcing (2*n+1)| + alpha*|delta (2*n+2)| + beta*|delta (2*n+1)| := by
        calc
          _ ≤ |forcing (2*n+1)| + |alpha*delta (2*n+2)| + |beta*delta (2*n+1)| := by
            simpa [sub_eq_add_neg, add_assoc] using
              (abs_add_three (forcing (2*n+1)) (-(alpha*delta (2*n+2))) (-(beta*delta (2*n+1))))
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hcoef.1, abs_of_nonneg hcoef.2.1]
      have hm : 0 ≤ m n := le_trans (abs_nonneg _) (le_max_left _ _)
      have hqle : alpha*q+beta ≤ q := by dsimp [q] at *; nlinarith
      nlinarith
    have hfpos : 0 ≤ f n := by
      dsimp [f]
      exact mul_nonneg (by linarith [hcoef.1]) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    rw [abs_of_nonneg hfpos]
    dsimp [m]
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    apply max_le <;> dsimp [f] at * <;> nlinarith [abs_nonneg (forcing (2*n)), abs_nonneg (forcing (2*n+1))]
  have hm : Tendsto m atTop (nhds 0) :=
    D5.S1.Recurrence.ComplementaryGoldenRatioLimit.vanishing_affine_error hq0 hq1
      (fun n => le_trans (abs_nonneg _) (le_max_left _ _)) hf (Eventually.of_forall hstep)
  apply Metric.tendsto_atTop.2
  intro epsilon hepsilon
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.1 hm epsilon hepsilon
  refine ⟨2*N,?_⟩
  intro n hn
  have hquot : N ≤ n/2 := by omega
  have hmn := hN (n/2) hquot
  have hbound : |delta n| ≤ m (n/2) := by
    have hrem := Nat.mod_lt n (by decide : 0<2)
    have hid := Nat.mod_add_div n 2
    rcases (show n%2=0 ∨ n%2=1 by omega) with h | h
    · have heq : n = 2*(n/2) := by omega
      conv_lhs => rw [heq]
      exact le_max_left _ _
    · have heq : n = 2*(n/2)+1 := by omega
      conv_lhs => rw [heq]
      exact le_max_right _ _
  have hmpos : 0 ≤ m (n/2) := le_trans (abs_nonneg _) (le_max_left _ _)
  simpa [Real.dist_eq, abs_of_nonneg hmpos] using lt_of_le_of_lt hbound (by simpa [Real.dist_eq, abs_of_nonneg hmpos] using hmn)

private theorem v_limit : Tendsto v atTop (nhds center) := by
  have h := delta_limit.add_const center
  simpa [delta] using h


private theorem square_ratio_limit :
    Tendsto (fun n => b (n+3) / b (n+2)) atTop (nhds tribonacciConstant) := by
  have hv1 := (tendsto_add_atTop_iff_nat 1).2 v_limit
  have h := (hv1.div v_limit center_pos.ne').mul proj_ratio_tendsto
  have heq (n : ℕ) : (v (n+1) / v n) * (proj (n+1) / proj n) = b (n+3) / b (n+2) := by
    dsimp [v]
    simp only [Nat.add_assoc, Nat.reduceAdd]
    field_simp [(proj_pos n).ne', (proj_pos (n+1)).ne', (b_pos (n+2)).ne']
  change Tendsto (fun n => (v (n+1) / v n) * (proj (n+1) / proj n))
    atTop (nhds ((center/center)*tribonacciConstant)) at h
  simp_rw [heq] at h
  simpa only [div_self center_pos.ne', one_mul] using h

private theorem ratio_limit :
    Tendsto (fun n : ℕ => (a (n+3) : ℝ) / a (n+2)) atTop (nhds rho) := by
  have hs := square_ratio_limit.sqrt
  have heq (n : ℕ) : Real.sqrt (b (n+3) / b (n+2)) = (a (n+5) : ℝ) / a (n+4) := by
    rw [Real.sqrt_div (b_pos _).le]
    simp [b, Real.sqrt_sq, Nat.add_assoc]
  simp_rw [heq] at hs
  exact (tendsto_add_atTop_iff_nat 2).1 (by simpa [rho, Nat.add_assoc] using hs)

/-- Source positive index `n` corresponds to zero-based index `n-1`. -/
def sourceA (n : ℕ) : ℕ := a (n-1)

/-- Exact published positive-index initial data and nearest-integer recurrence. -/
def sourceSpec (f : ℕ → ℕ) : Prop :=
  f 1 = 0 ∧ f 2 = 0 ∧ f 3 = 1 ∧ ∀ n : ℕ, 3 ≤ n →
    (f (n+1) : ℤ) = round (Real.sqrt
      ((f n ^ 2 + f (n-1) ^ 2 + f (n-2) ^ 2 : ℕ) : ℝ))

private theorem sourceRound_nearest_unique (s : ℕ) (j : ℤ)
    (hj : |Real.sqrt (s : ℝ) - (j : ℝ)| ≤ (1 : ℝ)/2) :
    j = (sourceRound s : ℤ) := by
  have hr := sourceRound_real_error s
  have hd : |(j : ℝ) - (sourceRound s : ℝ)| < 1 := by
    calc
      _ = |((j : ℝ) - Real.sqrt (s : ℝ)) +
          (Real.sqrt (s : ℝ) - (sourceRound s : ℝ))| := by congr 1; ring
      _ ≤ |(j : ℝ) - Real.sqrt (s : ℝ)| +
          |Real.sqrt (s : ℝ) - (sourceRound s : ℝ)| := abs_add_le _ _
      _ < 1 := by rw [abs_sub_comm (j : ℝ)]; linarith
  have hlo : (-1 : ℤ) < j - (sourceRound s : ℤ) := by
    exact_mod_cast (abs_lt.mp hd).1
  have hhi : j - (sourceRound s : ℤ) < (1 : ℤ) := by
    exact_mod_cast (abs_lt.mp hd).2
  omega

private theorem sourceRound_round (s : ℕ) :
    round (Real.sqrt (s : ℝ)) = (sourceRound s : ℤ) :=
  sourceRound_nearest_unique s _ (abs_sub_round _)

private theorem sourceA_spec : sourceSpec sourceA := by
  refine ⟨a_zero, a_one, a_two, ?_⟩
  intro n hn
  dsimp [sourceA]
  have heq : n = (n-3)+3 := by omega
  have h0 : n-1 = (n-3)+2 := by omega
  have h1 : n-1-1 = (n-3)+1 := by omega
  have h2 : n-2-1 = n-3 := by omega
  conv_lhs => rw [heq]
  rw [h1, h2, h0, a_recurrence]
  exact (sourceRound_round _).symm

private theorem source_unique {f : ℕ → ℕ} (hf : sourceSpec f) :
    ∀ n : ℕ, 1 ≤ n → f n = sourceA n := by
  have hrec (k : ℕ) : f (k+4) = sourceRound
      (f (k+3)^2 + f (k+2)^2 + f (k+1)^2) := by
    have h := hf.2.2.2 (k+3) (by omega)
    simp only [Nat.add_assoc, Nat.reduceAdd,
      show k+3-1 = k+2 by omega, show k+3-2 = k+1 by omega] at h
    rw [sourceRound_round] at h
    have hnat : f (k+4) = sourceRound
        (f (k+3)^2 + (f (k+2)^2 + f (k+1)^2)) := by exact_mod_cast h
    simpa only [Nat.add_assoc] using hnat
  have hu := a_unique (b := fun k => f (k+1)) hf.1 hf.2.1 hf.2.2.1 hrec
  intro n hn
  simpa [sourceA, show n-1+1 = n by omega] using hu (n-1)

/-- The complete infinite source claim, including construction, uniqueness,
positive denominators, exact rounding and the positive-index correspondence. -/
def targetClaim : Prop :=
  ∃ ρ : ℝ, 0 < ρ ∧
    (∀ x : ℝ, 0 < x → x^6-x^4-x^2-1 = 0 → x ≤ ρ) ∧
    Tendsto (fun n : ℕ => (a (n+3) : ℝ) / a (n+2)) atTop (nhds ρ) ∧
    ρ^6-ρ^4-ρ^2-1 = 0 ∧ sourceSpec sourceA ∧
    (∀ n : ℕ, 3 ≤ n → 0 < sourceA n) ∧
    (∀ f : ℕ → ℕ, sourceSpec f →
      (∀ n : ℕ, 1 ≤ n → f n = sourceA n) ∧
      Tendsto (fun n : ℕ => (f (n+4) : ℝ) / f (n+3)) atTop (nhds ρ))

/-- The exact OEIS A400644 infinite consecutive-ratio limit. -/
theorem result : targetClaim := by
  refine ⟨rho, rho_is_largest_positive_root.1,
    rho_is_largest_positive_root.2.2, ratio_limit,
    rho_is_largest_positive_root.2.1, sourceA_spec, ?_, ?_⟩
  · intro n hn
    have hp := a_pos (n-3)
    have heq : n-3+2 = n-1 := by omega
    dsimp [sourceA]
    rw [heq] at hp
    omega
  · intro f hf
    have hu := source_unique hf
    refine ⟨hu,?_⟩
    have heq (n : ℕ) : (f (n+4) : ℝ) / f (n+3) = (a (n+3) : ℝ) / a (n+2) := by
      rw [hu (n+4) (by omega), hu (n+3) (by omega)]
      simp [sourceA]
    simp_rw [heq]
    exact ratio_limit

end D5.S1.Recurrence.OEISA400644
