/- GID: D5/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass
   generality: I
   mirror-B: D5/B/S3/Weil/Mertens/IntegratedExplicit/QuarticSignedMass
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fourth-power chords preserve both signed Mangoldt masses with logarithmic error. -/

import D5.S3.Weil.Mertens.IntegratedExplicit.CompleteMangoldtLaplace
import D5.S3.Weil.Mertens.IntegratedExplicit.PrimeWindowPoleGrowth
import D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling
import Batteries.Tactic.OpenPrivate
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory Real
open D5.S3.Arith.Robin.CompleteMertensPeak (Q U)
open scoped Topology
open private log_tangent_bounds from D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSampling

namespace D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass

/-- The linear interpolant determined by the endpoint values on a cell. -/
def chord (f : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  (b - x) / (b - a) * f a + (x - a) / (b - a) * f b

private theorem chord_weights {a b x : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    let p := (b - x) / (b - a)
    let q := (x - a) / (b - a)
    0 ≤ p ∧ 0 ≤ q ∧ p + q = 1 ∧ p * a + q * b = x := by
  dsimp
  have hd := sub_pos.mpr hab
  refine ⟨div_nonneg (sub_nonneg.mpr hx.2) hd.le,
    div_nonneg (sub_nonneg.mpr hx.1) hd.le, ?_, ?_⟩
  · field_simp [hd.ne']
    ring
  · field_simp [hd.ne']
    ring

/-- The hinge chord gap is nonnegative and supported on strictly interior knots. -/
private theorem hinge_chord_gap {a b x k : ℝ} (hab : a < b) (hx : x ∈ Icc a b) :
    let gap := chord (fun z => max (z - k) 0) a b x - max (x - k) 0
    0 ≤ gap ∧ gap ≤ if k ∈ Ioo a b then b - a else 0 := by
  obtain ⟨hp, hq, hpq, hpx⟩ := chord_weights hab hx
  dsimp only
  by_cases hka : k ≤ a
  · rw [ite_eq_right (fun h : k ∈ Ioo a b => h.1.not_ge hka)]
    simp only [chord, max_eq_left (sub_nonneg.mpr hka),
      max_eq_left (sub_nonneg.mpr (hka.trans hx.1)),
      max_eq_left (sub_nonneg.mpr (hka.trans hab.le))]
    have he : (b - x) / (b - a) * (a - k) + (x - a) / (b - a) * (b - k) -
        (x - k) = 0 := by linear_combination hpx - k * hpq
    rw [he]
    exact ⟨le_rfl, le_rfl⟩
  by_cases hbk : b ≤ k
  · rw [ite_eq_right (fun h : k ∈ Ioo a b => h.2.not_ge hbk)]
    simp [chord, max_eq_right (sub_nonpos.mpr hbk),
      max_eq_right (sub_nonpos.mpr (hx.2.trans hbk)),
      max_eq_right (sub_nonpos.mpr (hab.le.trans hbk))]
  have hk : k ∈ Ioo a b := ⟨lt_of_not_ge hka, lt_of_not_ge hbk⟩
  rw [ite_eq_left hk]
  have hq1 : (x - a) / (b - a) ≤ 1 := by linarith
  simp only [chord, max_eq_right (sub_nonpos.mpr hk.1.le),
    max_eq_left (sub_nonneg.mpr hk.2.le), mul_zero, zero_add]
  constructor
  · apply sub_nonneg.mpr
    refine max_le ?_ (mul_nonneg hq (sub_nonneg.mpr hk.2.le))
    have hneg := mul_nonpos_of_nonneg_of_nonpos hp (sub_nonpos.mpr hk.1.le)
    have he : (b - x) / (b - a) * (a - k) + (x - a) / (b - a) * (b - k) =
        x - k := by linear_combination hpx - k * hpq
    linarith
  · have hle := mul_le_mul_of_nonneg_right hq1 (sub_nonneg.mpr hk.2.le)
    linarith [le_max_right (x - k) (0 : ℝ), hk.1]

/-- The coefficient of the actual von Mangoldt hinge. -/
def knotWeight (k : ℕ) : ℝ := ArithmeticFunction.vonMangoldt k / (k : ℝ)

/-- The total hinge coefficient of the knots strictly inside the cell. -/
def knotMass (a b : ℝ) : ℝ :=
  ∑ k ∈ (Finset.range (⌊b⌋₊ + 1)).filter (fun k : ℕ => (k : ℝ) ∈ Ioo a b), knotWeight k

private theorem knotWeight_nonneg (k : ℕ) : 0 ≤ knotWeight k :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg k)

private theorem knotMass_nonneg (a b : ℝ) : 0 ≤ knotMass a b :=
  Finset.sum_nonneg fun k _ => knotWeight_nonneg k

private theorem ramp_eq_hinge (k : ℕ) (z : ℝ) :
    mangoldtRamp k z = knotWeight k * max (z - k) 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [mangoldtRamp, knotWeight]
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hs : z / (k : ℝ) - 1 = (z - k) / (k : ℝ) := by
    rw [sub_div, div_self hk0.ne']
  unfold mangoldtRamp knotWeight
  have hm : max ((z - k) * (k : ℝ)⁻¹) 0 = max (z - k) 0 * (k : ℝ)⁻¹ := by
    simpa only [zero_mul] using
      (max_mul_of_nonneg (z - k) 0 (inv_nonneg.mpr hk0.le)).symm
  rw [hs]
  simp only [div_eq_mul_inv, hm]
  ring

/-- Only strictly interior Mangoldt hinges contribute to the arithmetic chord gap. -/
private theorem mangoldt_chord_gap {a b x : ℝ} (ha : 0 ≤ a) (hab : a < b) (hx : x ∈ Icc a b) :
    0 ≤ chord mangoldtPart a b x - mangoldtPart x ∧
      chord mangoldtPart a b x - mangoldtPart x ≤ (b - a) * knotMass a b := by
  classical
  let N := ⌊b⌋₊ + 1
  have hbN : b < (N : ℝ) := by simpa [N, Nat.cast_add] using Nat.lt_floor_add_one b
  have he : chord mangoldtPart a b x - mangoldtPart x =
      ∑ k ∈ Finset.range N, knotWeight k *
        (chord (fun z => max (z - k) 0) a b x - max (x - k) 0) := by
    unfold chord
    rw [mangoldtPart_eq_range ha (hab.trans hbN),
      mangoldtPart_eq_range (ha.trans hab.le) hbN,
      mangoldtPart_eq_range (ha.trans hx.1) (hx.2.trans_lt hbN)]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ramp_eq_hinge]
    ring
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (knotWeight_nonneg k) (hinge_chord_gap (k := k) hab hx).1
  · rw [knotMass, Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_le_sum fun k _ => ?_
    have h := mul_le_mul_of_nonneg_left (hinge_chord_gap (k := k) hab hx).2
      (knotWeight_nonneg k)
    split_ifs at h ⊢ with hk
    · simpa [mul_comm] using h
    · simpa using h

private theorem mul_log_chord_gap {a b x : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : x ∈ Icc a b) :
    0 ≤ chord (fun z => z * Real.log z) a b x - x * Real.log x ∧
      chord (fun z => z * Real.log z) a b x - x * Real.log x ≤ (b - a)^2 / a := by
  let p := (b - x) / (b - a)
  let q := (x - a) / (b - a)
  obtain ⟨hp, hq, hpq, hpx⟩ := chord_weights hab hx
  have hconv := Real.convexOn_mul_log.2
    (show a ∈ Ici (0 : ℝ) from ha.le)
    (show b ∈ Ici (0 : ℝ) from (ha.trans hab).le) hp hq hpq
  change (p * a + q * b) * Real.log (p * a + q * b) ≤
    p * (a * Real.log a) + q * (b * Real.log b) at hconv
  have hpx' : p * a + q * b = x := hpx
  rw [hpx'] at hconv
  change 0 ≤ p * (a * Real.log a) + q * (b * Real.log b) - x * Real.log x ∧
    p * (a * Real.log a) + q * (b * Real.log b) - x * Real.log x ≤ (b - a)^2 / a
  refine ⟨sub_nonneg.mpr hconv, ?_⟩
  let tangentError := fun z : ℝ => z * Real.log z - z * Real.log a - (z - a)
  have he : p * (a * Real.log a) + q * (b * Real.log b) - x * Real.log x =
      q * tangentError b - tangentError x := by
    dsimp [tangentError]
    linear_combination (Real.log a + 1) * hpx' - a * hpq
  rw [he]
  have hb := (log_tangent_bounds ha (ha.trans hab)).2
  have hx' := (log_tangent_bounds ha (ha.trans_le hx.1)).1
  have hq1 : q ≤ 1 := by change (x - a) / (b - a) ≤ 1; linarith
  exact (sub_le_self _ hx').trans
    ((mul_le_mul_of_nonneg_left hb hq).trans (by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right hq1 (div_nonneg (sq_nonneg _) ha.le)))

/-- The logarithmic and Mangoldt gaps give directional errors for the same chord. -/
private theorem U_sub_chord_bounds {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ∈ Icc a b) :
    -((b - a) * knotMass a b) ≤ U x - chord U a b x ∧
      U x - chord U a b x ≤ (b - a)^2 / a := by
  obtain ⟨hm0, hm⟩ := mangoldt_chord_gap ha.le hab hx
  obtain ⟨hl0, hl⟩ := mul_log_chord_gap ha hab hx
  have he : U x - chord U a b x =
      (chord (fun z => z * Real.log z) a b x - x * Real.log x) -
      (chord mangoldtPart a b x - mangoldtPart x) := by
    have h := (chord_weights hab hx).2.2.2
    unfold chord
    rw [U_eq_complete_ramps (ha.trans_le hx.1).le, U_eq_complete_ramps ha.le,
      U_eq_complete_ramps (ha.trans hab).le]
    linear_combination -(1 + Real.eulerMascheroniConstant) * h
  rw [he]
  exact ⟨by linarith, by linarith⟩

/-- The pointwise error for the literal complete Mertens ramp on one cell. -/
private theorem abs_U_sub_chord_le {a b x : ℝ} (ha : 0 < a) (hab : a < b) (hx : x ∈ Icc a b) :
    |U x - chord U a b x| ≤ (b - a)^2 / a + (b - a) * knotMass a b := by
  obtain ⟨hl, hu⟩ := U_sub_chord_bounds ha hab hx
  exact abs_le.mpr ⟨by linarith [div_nonneg (sq_nonneg (b - a)) ha.le],
    by linarith [mul_nonneg (sub_nonneg.mpr hab.le) (knotMass_nonneg a b)]⟩

/-- For `s = 1` or `s = -1` this is the weighted positive or negative part. -/
def signedDensity (s : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (s * f x) 0 * x ^ (-(3 / 2) : ℝ)

private theorem density_intervalIntegrable {s a b : ℝ} {f : ℝ → ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hf : ContinuousOn f (Icc a b)) :
    IntervalIntegrable (signedDensity s f) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  have hsf : ContinuousOn (fun x => s * f x) (Icc a b) := continuousOn_const.mul hf
  exact (hsf.sup continuousOn_const).mul <|
    continuousOn_id.rpow_const fun x hx => Or.inl (ha.trans_le hx.1).ne'

/-- The positive and negative integrals of the chord have the same weighted cell budget. -/
private theorem signed_cell_error {s a b : ℝ} (hs : |s| ≤ 1) (ha : 0 < a) (hab : a < b) :
    |(∫ x in a..b, signedDensity s U x) -
      (∫ x in a..b, signedDensity s (chord U a b) x)| ≤
      (b - a) * (((b - a)^2 / a + (b - a) * knotMass a b) * a ^ (-(3 / 2) : ℝ)) := by
  let E := (b - a)^2 / a + (b - a) * knotMass a b
  have hE : 0 ≤ E := add_nonneg (div_nonneg (sq_nonneg _) ha.le)
    (mul_nonneg (sub_nonneg.mpr hab.le) (knotMass_nonneg a b))
  have hU : ContinuousOn U (Icc a b) := fun _ hx =>
    (U_continuousAt_pos (ha.trans_le hx.1)).continuousWithinAt
  have hch : Continuous (chord U a b) := by unfold chord; fun_prop
  have hf := density_intervalIntegrable (s := s) ha hab.le hU
  have hg := density_intervalIntegrable (s := s) ha hab.le hch.continuousOn
  rw [← intervalIntegral.integral_sub hf hg]
  refine (intervalIntegral.abs_integral_le_integral_abs hab.le).trans ?_
  have hi := intervalIntegral.integral_mono_on hab.le (hf.sub hg).abs
    (intervalIntegrable_const (c := E * a ^ (-(3 / 2) : ℝ))) ?_
  · simpa only [intervalIntegral.integral_const, smul_eq_mul] using hi
  intro x hx
  have hw : 0 ≤ x ^ (-(3 / 2) : ℝ) := Real.rpow_nonneg (ha.trans_le hx.1).le _
  have hweight := Real.rpow_le_rpow_of_nonpos ha hx.1 (by norm_num : -(3 / 2 : ℝ) ≤ 0)
  have hmax : |max (s * U x) 0 - max (s * chord U a b x) 0| ≤ E := calc
    _ ≤ |s * U x - s * chord U a b x| := abs_max_sub_max_le_abs _ _ 0
    _ = |s| * |U x - chord U a b x| := by rw [← mul_sub, abs_mul]
    _ ≤ 1 * |U x - chord U a b x| := mul_le_mul_of_nonneg_right hs (abs_nonneg _)
    _ ≤ E := by simpa only [one_mul] using abs_U_sub_chord_le ha hab hx
  rw [signedDensity, signedDensity, ← sub_mul, abs_mul, abs_of_nonneg hw]
  exact (mul_le_mul_of_nonneg_right hmax hw).trans (mul_le_mul_of_nonneg_left hweight hE)

/-- The fourth-power grid in the original variable of the Mertens ramp. -/
def grid (n : ℕ) : ℝ := (n : ℝ)^4

private theorem grid_strictMono : StrictMono grid := by
  intro n m hnm
  unfold grid
  have h : (n : ℝ) < (m : ℝ) := by exact_mod_cast hnm
  gcongr

private theorem grid_pos {n : ℕ} (hn : 1 ≤ n) : 0 < grid n :=
  (show (0 : ℝ) = grid 0 by norm_num [grid]) ▸
    grid_strictMono (show 0 < n by omega)

private theorem grid_step_le {n : ℕ} (hn : 1 ≤ n) :
    grid (n + 1) - grid n ≤ 15 * (n : ℝ)^3 := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast hn
  unfold grid
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg (n : ℝ)),
    mul_nonneg (sub_nonneg.mpr h) (Nat.cast_nonneg n)]

/-- The budget is `3375/n` plus `225` times the interior Mangoldt mass. -/
private theorem quartic_cell_error {s : ℝ} (hs : |s| ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    |(∫ x in grid n..grid (n + 1), signedDensity s U x) -
      (∫ x in grid n..grid (n + 1), signedDensity s (chord U (grid n) (grid (n + 1))) x)| ≤
      3375 / (n : ℝ) + 225 * knotMass (grid n) (grid (n + 1)) := by
  let a := grid n
  let b := grid (n + 1)
  let M := knotMass a b
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < a := grid_pos hn
  have hab : a < b := grid_strictMono (Nat.lt_succ_self n)
  have hstep : b - a ≤ 15 * (n : ℝ)^3 := grid_step_le hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (b - a)^2 / a ≤ 225 * (n : ℝ)^2 := by
    simpa only [a, b, grid, Nat.cast_succ] using
      QuarticSampling.quartic_chord_error (n := (n : ℝ)) (a := (n : ℝ)^4)
        (z := ((n : ℝ) + 1)^4) hnR le_rfl
        (by simpa only [a, b, grid, Nat.cast_succ] using hab.le) le_rfl
  have hw : a ^ (-(3 / 2) : ℝ) = ((n : ℝ)^6)⁻¹ := by
    dsimp [a, grid]
    rw [← Real.rpow_natCast_mul hn0.le 4]
    norm_num [Real.rpow_neg hn0.le]
  refine (signed_cell_error hs ha hab).trans ?_
  change (b - a) * (((b - a)^2 / a + (b - a) * M) * a ^ (-(3 / 2) : ℝ)) ≤
    3375 / (n : ℝ) + 225 * M
  rw [hw]
  have hM : 0 ≤ M := knotMass_nonneg a b
  calc
    _ ≤ (15 * (n : ℝ)^3) *
        ((225 * (n : ℝ)^2 + (15 * (n : ℝ)^3) * M) * ((n : ℝ)^6)⁻¹) := by
      gcongr
    _ = _ := by
      field_simp [hn0.ne']
      ring

/-- The weighted mass of the chords computed from the finite array of endpoint values. -/
def gridChordMass (s : ℝ) (A B : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico A B,
    ∫ x in grid n..grid (n + 1), signedDensity s (chord U (grid n) (grid (n + 1))) x

/-- Both signs of the actual weighted integral are approximated by the endpoint chords,
with the sum of the localized hinge budgets as the finite error. -/
private theorem quartic_grid_error {s : ℝ} (hs : |s| ≤ 1) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |(∫ x in grid A..grid B, signedDensity s U x) - gridChordMass s A B| ≤
      ∑ n ∈ Finset.Ico A B, (3375 / (n : ℝ) + 225 * knotMass (grid n) (grid (n + 1))) := by
  have hint (n : ℕ) (hn : n ∈ Ico A B) :
      IntervalIntegrable (signedDensity s U) volume (grid n) (grid (n + 1)) := by
    have hpos := grid_pos (hA.trans hn.1)
    exact density_intervalIntegrable hpos (grid_strictMono.monotone (Nat.le_succ n))
      (fun _ hx => (U_continuousAt_pos (hpos.trans_le hx.1)).continuousWithinAt)
  rw [← intervalIntegral.sum_integral_adjacent_intervals_Ico hAB hint, gridChordMass,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
  exact quartic_cell_error hs (hA.trans (Finset.mem_Ico.mp hn).1)

private def mangoldtPrefix (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 0 ⌊x⌋₊, knotWeight k

private theorem knotMass_le_prefix_sub {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    knotMass a b ≤ mangoldtPrefix b - mangoldtPrefix a := by
  have hfloor : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hsum :
      mangoldtPrefix a + ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, knotWeight k =
        mangoldtPrefix b := by
    unfold mangoldtPrefix
    rw [← Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl),
      Finset.Ioc_union_Ioc_eq_Ioc (Nat.zero_le _) hfloor]
  apply le_sub_iff_add_le.mpr
  rw [add_comm, ← hsum]
  gcongr
  unfold knotMass
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => knotWeight_nonneg k)
  intro k hk
  have h : (k : ℝ) ∈ Ioo a b := (Finset.mem_filter.mp hk).2
  exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt ha).2 h.1,
    (Nat.le_floor_iff (ha.trans hab)).2 h.2.le⟩

private theorem sum_cell_differences (f : ℕ → ℝ) {A B : ℕ} (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ico A B, (f (n + 1) - f n)) = f B - f A := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [Finset.sum_Ico_succ_top hn, ih]
    ring

/-- The disjoint open-cell charges are bounded by a single Mangoldt prefix difference.
The half-open prefix difference can also charge grid endpoints. -/
private theorem sum_quartic_knotMass_le {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ico A B, knotMass (grid n) (grid (n + 1))) ≤
      4 * (Real.log (B : ℝ) - Real.log (A : ℝ)) +
        (Mertens.E₁Λ (grid B) - Mertens.E₁Λ (grid A)) := by
  have hprefix (n : ℕ) : mangoldtPrefix (grid n) =
      4 * Real.log (n : ℝ) + Mertens.E₁Λ (grid n) := by
    calc
      _ = Real.log (grid n) + Mertens.E₁Λ (grid n) :=
        Mertens.sum_mangoldt_div_eq _
      _ = _ := by rw [grid, Real.log_pow]; norm_num
  calc
    _ ≤ ∑ n ∈ Finset.Ico A B, (mangoldtPrefix (grid (n + 1)) - mangoldtPrefix (grid n)) :=
      Finset.sum_le_sum fun n hn =>
        knotMass_le_prefix_sub (grid_pos (hA.trans (Finset.mem_Ico.mp hn).1)).le
          (grid_strictMono.monotone (Nat.le_succ n))
    _ = _ := by
      have ht := sum_cell_differences (mangoldtPrefix ∘ grid) hAB
      simp only [Function.comp_apply] at ht
      rw [ht, hprefix, hprefix]
      ring

private theorem sum_inv_le_log {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ico A B, (n : ℝ)⁻¹) ≤
      Real.log (B : ℝ) - Real.log (A : ℝ) + (A : ℝ)⁻¹ - (B : ℝ)⁻¹ := by
  let f := fun n : ℕ => Real.log (n : ℝ) - (n : ℝ)⁻¹
  calc
    _ ≤ ∑ n ∈ Finset.Ico A B, (f (n + 1) - f n) := by
      refine Finset.sum_le_sum fun n hn => ?_
      have hn0 : (0 : ℝ) < n := by
        exact_mod_cast (show 0 < n from hA.trans (Finset.mem_Ico.mp hn).1)
      have hs : 0 < (n : ℝ) + 1 := by positivity
      have hlog := Real.one_sub_inv_le_log_of_pos (div_pos hs hn0)
      rw [Real.log_div hs.ne' hn0.ne', inv_div] at hlog
      have he : 1 - (n : ℝ) / (n + 1) = ((n : ℝ) + 1)⁻¹ := by
        field_simp [hs.ne']
        ring
      rw [he] at hlog
      dsimp [f]
      push_cast
      linarith
    _ = _ := by rw [sum_cell_differences f hAB]; dsimp [f]; ring

/-- The endpoint chords preserve the weighted positive and negative masses up to
an error logarithmic in the ratio of the grid indices, with an explicit constant. -/
theorem quartic_grid_log_error {s : ℝ} (hs : |s| ≤ 1) {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    |(∫ x in grid A..grid B, signedDensity s U x) - gridChordMass s A B| ≤
      4275 * (Real.log (B : ℝ) - Real.log (A : ℝ)) +
        3375 / (A : ℝ) + 225 * (Real.log 4 + 6) := by
  have hgrid (n : ℕ) (hn : 1 ≤ n) : 1 ≤ grid n :=
    (show (1 : ℝ) = grid 1 by norm_num [grid]) ▸ grid_strictMono.monotone hn
  have hlow := Mertens.E₁Λ.ge (hgrid A hA)
  have hhigh := Mertens.E₁Λ.le (hgrid B (hA.trans hAB))
  have hk := sum_quartic_knotMass_le hA hAB
  have hlog := sum_inv_le_log hA hAB
  refine (quartic_grid_error hs hA hAB).trans ?_
  simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.mul_sum]
  linarith [inv_nonneg.mpr (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]

/-- Weighted mass of either sign of the complete ramp. -/
private def mass (sign lower upper : ℝ) : ℝ :=
  ∫ x in lower..upper, max (sign * U x) 0 / x / Real.sqrt x

private theorem mass_eq_tail {sign lower upper : ℝ} (hL : 2 ≤ lower)
    (hLU : lower ≤ upper) :
    mass sign lower upper = ∫ x in lower..upper, max (sign * (-Q x)) 0 / Real.sqrt x := by
  unfold mass
  apply intervalIntegral.integral_congr
  intro x hx
  have hx₂ := hL.trans ((uIcc_of_le hLU) ▸ hx).1
  have hx₀ : 0 < x := by linarith
  have ht := D5.S3.Weil.Mertens.CompleteChebyshevTailIdentity.complete_chebyshev_tail_identity
    D5.S3.Weil.Mertens.WeightedPrimeLimit.chebyshev_error_kernel_integrable hx₂
  change Q x = _ at ht
  have hU : -Q x = U x / x := by
    rw [ht]
    dsimp only [U]
    field_simp [hx₀.ne']
    ring
  change max (sign * U x) 0 / x / Real.sqrt x = max (sign * (-Q x)) 0 / Real.sqrt x
  rw [hU, ← mul_div_assoc, ← max_div_div_right hx₀.le (sign * U x) 0, zero_div]

private theorem log_error_absorbed (C : ℝ) (hC : 0 ≤ C) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ x : ℝ in atTop, C * (1 + Real.log x) ≤ x ^ p := by
  have hpos : 0 < 2 * (C + 1) := by linarith
  have hl := (isLittleO_log_rpow_atTop hp).bound (inv_pos.mpr hpos)
  filter_upwards [hl, eventually_ge_atTop (1 : ℝ),
    (tendsto_rpow_atTop hp).eventually_ge_atTop (2 * (C + 1))] with x hx hx₁ hlarge
  have hx₀ := zero_lt_one.trans_le hx₁
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx₁),
    abs_of_pos (Real.rpow_pos_of_pos hx₀ _)] at hx
  rw [← div_eq_inv_mul] at hx
  have hlog := (le_div_iff₀ hpos).mp hx
  nlinarith [mul_nonneg hC (Real.log_nonneg hx₁)]

/-- Any uniform logarithmic approximation to signed mass on fourth-power
blocks retains the off-line zero's exponent, for both signs on the same blocks. -/
private theorem sampled_power_lower {z : ℂ} (hz : riemannZeta z = 0) (hβ : 1 / 2 < z.re)
    (approximation : ℝ → ℕ → ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (happrox : ∀ᶠ k : ℕ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      mass sign ((k : ℝ)^12) ((k : ℝ)^16) ≤ approximation sign (k^3) (k^4) +
        C * (1 + Real.log (k : ℝ)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      (k : ℝ) ^ (16 * (z.re - 1 / 2) - ε) ≤ approximation sign (k^3) (k^4) := by
  let gap := z.re - 1 / 2
  have hgap : 0 < gap := sub_pos.mpr hβ
  let δ := min (ε/2) (4*gap)
  have hδ : 0 < δ := lt_min (half_pos hε) (by positivity)
  have hδε : 2*δ ≤ ε := by linarith [min_le_left (ε/2) (4*gap)]
  have hδg : δ ≤ 4*gap := min_le_right _ _
  let p := 16*gap-2*δ
  have hp : 0 < p := by dsimp [p]; linarith
  have hlow := PrimeWindowPoleGrowth.off_line_zero_forces_signed_complete_window_mass hz hβ
    (b := (4 : ℝ)/3) (by norm_num) (div_pos hδ (by norm_num : (0 : ℝ) < 12))
  have hY : Tendsto (fun k : ℕ => (k : ℝ)^12) atTop atTop :=
    (tendsto_pow_atTop (by decide : (12 : ℕ) ≠ 0)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hY.eventually hlow, happrox, eventually_ge_atTop (2 : ℕ),
    tendsto_natCast_atTop_atTop.eventually (log_error_absorbed C hC hp),
    tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hδ).eventually_ge_atTop 2)]
    with k hk happ hk₂ hlog hbig sign hs
  have hk₁ : 1 ≤ (k : ℝ) := by exact_mod_cast (show 1 ≤ k by omega)
  have hk₀ := zero_lt_one.trans_le hk₁
  have hstart : (2 : ℝ) ≤ (k : ℝ)^12 := by
    exact (by exact_mod_cast hk₂ : (2 : ℝ) ≤ (k : ℝ)).trans (le_self_pow₀ hk₁ (by decide))
  have hstop : ((k : ℝ)^12)^((4 : ℝ)/3) = (k : ℝ)^16 := by
    rw [← Real.rpow_natCast (k : ℝ) 12, ← Real.rpow_mul hk₀.le]
    norm_num
  have hend : (k : ℝ)^12 ≤ (k : ℝ)^16 := pow_le_pow_right₀ hk₁ (by decide)
  have hpow : ((k : ℝ)^12)^((4 : ℝ)/3*(z.re-1 / 2)-δ/12) =
      (k : ℝ)^p*(k : ℝ)^δ := by
    rw [← Real.rpow_natCast (k : ℝ) 12, ← Real.rpow_mul hk₀.le, ← Real.rpow_add hk₀]
    congr 1
    dsimp [p, gap]
    ring
  have hlower := hk sign hs
  rw [hstop, hpow, ← mass_eq_tail hstart hend] at hlower
  have hcomparison := happ sign hs
  have hdouble := mul_le_mul_of_nonneg_left hbig (Real.rpow_nonneg hk₀.le p)
  have hgoal : (k : ℝ)^(16*(z.re-1 / 2)-ε) ≤ (k : ℝ)^p :=
    Real.rpow_le_rpow_of_exponent_le hk₁ (by change 16*gap-ε ≤ 16*gap-2*δ; linarith)
  exact hgoal.trans (by nlinarith only [hlower, hcomparison, hdouble, hlog])

private theorem mass_eq_signedDensity {sign lower upper : ℝ} (hL : 0 < lower)
    (hLU : lower ≤ upper) :
    mass sign lower upper = ∫ x in lower..upper, signedDensity sign U x := by
  unfold mass
  apply intervalIntegral.integral_congr
  intro x hx
  have hx₀ := hL.trans_le ((uIcc_of_le hLU) ▸ hx).1
  have hpow : x ^ (-(3/2):ℝ) = (x ^ (1:ℝ))⁻¹ * (x ^ (1 / 2:ℝ))⁻¹ := by
    rw [← Real.rpow_neg hx₀.le, ← Real.rpow_neg hx₀.le, ← Real.rpow_add hx₀]
    congr 1
    norm_num
  rw [Real.rpow_one, ← Real.sqrt_eq_rpow] at hpow
  change max (sign * U x) 0 / x / Real.sqrt x = max (sign * U x) 0 * x ^ (-(3 / 2) : ℝ)
  rw [hpow, div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

/-- An off-line zero forces both signed chord masses to have power-sized growth on
every sufficiently late fourth-power block, with no power lost to discretization. -/
theorem off_line_zero_forces_signed_quartic_chord_mass
    {z : ℂ} (hz : riemannZeta z = 0) (hβ : 1 / 2 < z.re) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ sign : ℝ, sign = 1 ∨ sign = -1 →
      (k : ℝ) ^ (16 * (z.re - 1 / 2) - ε) ≤ gridChordMass sign (k^3) (k^4) := by
  apply sampled_power_lower hz hβ gridChordMass 6000 (by norm_num) _ hε
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with k hk sign hs
  have hkR : 1 ≤ (k : ℝ) := by exact_mod_cast hk
  have hk₀ := zero_lt_one.trans_le hkR
  have hsign : |sign| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hA : 1 ≤ k^3 := one_le_pow₀ hk
  have hAB : k^3 ≤ k^4 := pow_le_pow_right₀ hk (by decide)
  have heA : grid (k^3) = (k : ℝ)^12 := by simp [grid, ← pow_mul]
  have heB : grid (k^4) = (k : ℝ)^16 := by simp [grid, ← pow_mul]
  have hab : (k : ℝ)^12 ≤ (k : ℝ)^16 := pow_le_pow_right₀ hkR (by decide)
  have h := (abs_le.mp (quartic_grid_log_error hsign hA hAB)).2
  rw [heA, heB, ← mass_eq_signedDensity (pow_pos hk₀ 12) hab] at h
  have hlog : Real.log ((k^4:ℕ):ℝ) - Real.log ((k^3:ℕ):ℝ) = Real.log (k : ℝ) := by
    push_cast
    rw [Real.log_pow, Real.log_pow]
    norm_num
    ring
  rw [hlog] at h
  have hlog4 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
  have hd : 3375 / ((k^3:ℕ):ℝ) ≤ 3375 := by
    have hh : 1 ≤ ((k^3:ℕ):ℝ) := by exact_mod_cast hA
    apply (div_le_iff₀ (zero_lt_one.trans_le hh)).2
    linarith
  linarith [Real.log_nonneg hkR]

end D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass

#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.quartic_grid_log_error
#print axioms D5.S3.Weil.Mertens.IntegratedExplicit.QuarticSignedMass.off_line_zero_forces_signed_quartic_chord_mass
