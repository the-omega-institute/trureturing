/- GID: D5/S3/CharacterSums/DirichletJointPositiveWindow
   generality: I
   mirror-B: D5/B/S3/CharacterSums/DirichletJointPositiveWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Finite integer chords bound the weighted positive mass of the joint Dirichlet ramp. -/

import D5.S3.CharacterSums.DirichletRampEndpoint
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Tactic

/-! Finite positive-window bounds for the complete zeta ramp and a signed
nonprincipal Dirichlet ramp. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators Topology

namespace DirichletPositiveWindowChord

/-- A finite ramp truncated at a fixed integer. On a window below the cutoff, terms
above the moving floor vanish. The linear centering coefficient is arbitrary. -/
private def centeredRamp (M : ℕ) (q : ℕ → ℝ) (A k x : ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 M, q n * max (x / (n : ℝ) - 1) 0) -
    A * (x * Real.log x) + k * x

def chord (f : ℝ → ℝ) (l u x : ℝ) : ℝ :=
  (u - x) / (u - l) * f l + (x - l) / (u - l) * f u

def weight (x : ℝ) : ℝ := x ^ (-(3 / 2) : ℝ)

def positiveDensity (f : ℝ → ℝ) (x : ℝ) : ℝ := max (f x) 0 * weight x

private theorem convex_quadratic_sub_mul_log {l u : ℝ} (hl : 0 < l) :
    ConvexOn ℝ (Icc l u) (fun x => (1 / (2 * l)) * x ^ 2 - x * Real.log x) := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc l u)
    ((continuous_const.mul (continuous_id.pow 2)).sub Real.continuous_mul_log).continuousOn
    (f' := fun x => x / l - (Real.log x + 1))
    (f'' := fun x => 1 / l - x⁻¹) ?_ ?_ ?_
  · intro x hx
    have hx0 : 0 < x := hl.trans_le (interior_subset hx).1
    have hp := ((hasDerivAt_id' (x := x)).mul (hasDerivAt_id' (x := x))).const_mul
      (1 / (2 * l))
    have h := hp.sub (Real.hasDerivAt_mul_log hx0.ne')
    have hderiv : (1 / (2 * l)) * (1 * x + x * 1) - (Real.log x + 1) =
        x / l - (Real.log x + 1) := by
      field_simp [hl.ne'] <;> ring
    have h' := h.congr_deriv hderiv
    refine (h'.congr_of_eventuallyEq ?_).hasDerivWithinAt
    filter_upwards with y
    change (1 / (2 * l)) * y ^ 2 - y * Real.log y =
      (1 / (2 * l)) * (y * y) - y * Real.log y
    rw [pow_two]
  · intro x hx
    have hx0 : 0 < x := hl.trans_le (interior_subset hx).1
    exact (((hasDerivAt_id' (x := x)).div_const l).sub
      ((Real.hasDerivAt_log hx0.ne').add_const 1)).hasDerivWithinAt
  · intro x hx
    have hlx : l ≤ x := (interior_subset hx).1
    exact sub_nonneg.mpr (by
      rw [← one_div x]
      exact div_le_div_of_nonneg_left zero_le_one hl hlx)

private theorem ramp_sum_chord {M : ℕ} {q : ℕ → ℝ} {l u x a b : ℝ}
    (hx : x ∈ Icc l u) (hab : a + b = 1) (hm : a * l + b * u = x)
    (hknots : ∀ n ∈ Finset.Ioc 0 M, (n : ℝ) ∈ Ioo l u → q n = 0) :
    (∑ n ∈ Finset.Ioc 0 M, q n * max (x / (n : ℝ) - 1) 0) =
      a * (∑ n ∈ Finset.Ioc 0 M, q n * max (l / (n : ℝ) - 1) 0) +
      b * (∑ n ∈ Finset.Ioc 0 M, q n * max (u / (n : ℝ) - 1) 0) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
  by_cases hnl : (n : ℝ) ≤ l
  · have active (t : ℝ) (ht : (n : ℝ) ≤ t) : max (t / (n : ℝ) - 1) 0 =
        t / (n : ℝ) - 1 :=
      max_eq_left (sub_nonneg.mpr ((one_le_div hn0).mpr ht))
    rw [active x (hnl.trans hx.1), active l hnl, active u (hnl.trans (hx.1.trans hx.2))]
    rw [← hm]
    linear_combination (q n) * hab
  by_cases hun : u ≤ (n : ℝ)
  · have inactive (t : ℝ) (ht : t ≤ (n : ℝ)) : max (t / (n : ℝ) - 1) 0 = 0 :=
      max_eq_right (sub_nonpos.mpr ((div_le_one hn0).mpr ht))
    rw [inactive x (hx.2.trans hun), inactive l (hx.1.trans (hx.2.trans hun)), inactive u hun]
    simp
  · simp [hknots n hn ⟨lt_of_not_ge hnl, lt_of_not_ge hun⟩]

/-- The finite ramp can have signed coefficients. Its only curvature on the cell
comes from the principal logarithmic term. Zero coefficients can be skipped. -/
private theorem centeredRamp_chord_gap {M : ℕ} {q : ℕ → ℝ} {A k l u x : ℝ}
    (hA : 0 ≤ A) (hl : 0 < l) (hlu : l < u) (hx : x ∈ Icc l u)
    (hknots : ∀ n ∈ Finset.Ioc 0 M, (n : ℝ) ∈ Ioo l u → q n = 0) :
    0 ≤ centeredRamp M q A k x - chord (centeredRamp M q A k) l u x ∧
    centeredRamp M q A k x - chord (centeredRamp M q A k) l u x ≤
      A / (2 * l) * (x - l) * (u - x) := by
  let a := (u - x) / (u - l)
  let b := (x - l) / (u - l)
  have hd : 0 < u - l := sub_pos.mpr hlu
  have ha : 0 ≤ a := div_nonneg (sub_nonneg.mpr hx.2) hd.le
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hx.1) hd.le
  have hab : a + b = 1 := by dsimp [a, b]; field_simp [hd.ne'] <;> ring
  have hm : a * l + b * u = x := by dsimp [a, b]; field_simp [hd.ne'] <;> ring
  have h1 := Real.convexOn_mul_log.2
    (show l ∈ Ici (0 : ℝ) from hl.le) (show u ∈ Ici (0 : ℝ) from hl.le.trans hlu.le) ha hb hab
  change (a * l + b * u) * Real.log (a * l + b * u) ≤
    a * (l * Real.log l) + b * (u * Real.log u) at h1
  rw [hm] at h1
  have h2 := (convex_quadratic_sub_mul_log (u := u) hl).2
    (show l ∈ Icc l u from ⟨le_rfl, hlu.le⟩)
    (show u ∈ Icc l u from ⟨hlu.le, le_rfl⟩) ha hb hab
  change (1 / (2 * l)) * (a * l + b * u) ^ 2 -
    (a * l + b * u) * Real.log (a * l + b * u) ≤
    a * ((1 / (2 * l)) * l ^ 2 - l * Real.log l) +
      b * ((1 / (2 * l)) * u ^ 2 - u * Real.log u) at h2
  rw [hm] at h2
  have hquad : a * l ^ 2 + b * u ^ 2 - x ^ 2 = (x - l) * (u - x) := by
    dsimp [a, b]
    field_simp [hd.ne'] <;> ring
  have hlog : a * (l * Real.log l) + b * (u * Real.log u) - x * Real.log x ≤
      (1 / (2 * l)) * ((x - l) * (u - x)) := by
    rw [← hquad]
    linear_combination h2
  have hgap : centeredRamp M q A k x - chord (centeredRamp M q A k) l u x =
      A * (a * (l * Real.log l) + b * (u * Real.log u) - x * Real.log x) := by
    change centeredRamp M q A k x -
      (a * centeredRamp M q A k l + b * centeredRamp M q A k u) = _
    unfold centeredRamp
    rw [ramp_sum_chord hx hab hm hknots]
    linear_combination -k * hm
  rw [hgap]
  constructor
  · exact mul_nonneg hA (sub_nonneg.mpr h1)
  · calc
      _ ≤ A * ((1 / (2 * l)) * ((x - l) * (u - x))) :=
        mul_le_mul_of_nonneg_left hlog hA
      _ = _ := by field_simp [hl.ne'] <;> ring

private theorem continuous_centeredRamp (M : ℕ) (q : ℕ → ℝ) (A k : ℝ) :
    Continuous (centeredRamp M q A k) := by
  unfold centeredRamp
  apply Continuous.add
  · apply Continuous.sub
    · exact continuous_finsetSum _ fun n _ => by fun_prop
    · exact continuous_const.mul Real.continuous_mul_log
  · fun_prop

private theorem continuousOn_weight {l u : ℝ} (hl : 0 < l) :
    ContinuousOn weight (Icc l u) := by
  exact continuousOn_id.rpow_const fun x hx => Or.inl (hl.trans_le hx.1).ne'

private theorem intervalIntegrable_density {f : ℝ → ℝ} {l u : ℝ}
    (hf : Continuous f) (hl : 0 < l) (hlu : l ≤ u) :
    IntervalIntegrable (positiveDensity f) volume l u := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hlu]
  exact (hf.max continuous_const).continuousOn.mul (continuousOn_weight hl)

private theorem integral_weight {l u : ℝ} (hl : 0 < l) (hlu : l ≤ u) :
    (∫ x in l..u, weight x) = 2 * (l ^ (-(1 / 2) : ℝ) - u ^ (-(1 / 2) : ℝ)) := by
  have hz : (0 : ℝ) ∉ uIcc l u := by
    rw [uIcc_of_le hlu]
    exact fun h => hl.not_ge h.1
  unfold weight
  rw [integral_rpow (r := -(3 / 2 : ℝ)) (Or.inr ⟨by norm_num, hz⟩),
    show -(3 / 2 : ℝ) + 1 = -(1 / 2 : ℝ) by norm_num]
  ring

/-- The positive-part density is squeezed by the chord and a universal cell error. -/
private theorem centeredRamp_density_bounds {M : ℕ} {q : ℕ → ℝ} {A k Y l u x : ℝ}
    (hA : 0 ≤ A) (hY : 0 < Y) (hYl : Y ≤ l) (hlu : l < u) (hlen : u - l ≤ 1)
    (hx : x ∈ Icc l u)
    (hknots : ∀ n ∈ Finset.Ioc 0 M, (n : ℝ) ∈ Ioo l u → q n = 0) :
    positiveDensity (chord (centeredRamp M q A k) l u) x ≤
      positiveDensity (centeredRamp M q A k) x ∧
    positiveDensity (centeredRamp M q A k) x ≤
      positiveDensity (chord (centeredRamp M q A k) l u) x + (A / (8 * Y)) * weight x := by
  have hl := hY.trans_le hYl
  obtain ⟨hlo, hhi⟩ := centeredRamp_chord_gap hA hl hlu hx hknots (k := k)
  have hp : (x - l) * (u - x) ≤ (1 : ℝ) / 4 := by
    have hd : 0 ≤ u - l := sub_nonneg.mpr hlu.le
    have hm := mul_nonneg (sub_nonneg.mpr hlen) (show 0 ≤ 1 + (u - l) by linarith)
    nlinarith only [hm, sq_nonneg (2 * x - l - u)]
  have hscale : (A / (2 * l)) ≤ A / (2 * Y) := by
    exact div_le_div_of_nonneg_left hA (by positivity) (mul_le_mul_of_nonneg_left hYl (by norm_num))
  have he : (0 : ℝ) ≤ A / (8 * Y) := by positivity
  have herr : centeredRamp M q A k x - chord (centeredRamp M q A k) l u x ≤ A / (8 * Y) :=
    calc
      _ ≤ _ := hhi
      _ = (A / (2 * l)) * ((x - l) * (u - x)) := by ring
      _ ≤ (A / (2 * l)) * (1 / 4) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ (A / (2 * Y)) * (1 / 4) := mul_le_mul_of_nonneg_right hscale (by norm_num)
      _ = _ := by field_simp [hY.ne'] <;> ring
  have hw : 0 ≤ weight x := Real.rpow_nonneg (hl.le.trans hx.1) _
  unfold positiveDensity
  constructor
  · exact mul_le_mul_of_nonneg_right (max_le_max (sub_nonneg.mp hlo) le_rfl) hw
  · rw [← add_mul]
    refine mul_le_mul_of_nonneg_right (max_le ?_ ?_) hw
    · have h := le_max_left (chord (centeredRamp M q A k) l u x) (0 : ℝ)
      linarith only [herr, h]
    · exact add_nonneg (le_max_right _ _) he

/-- On one cell the integrated error retains the exact difference of inverse
square roots at the endpoints. -/
private theorem centeredRamp_cell_integral_bounds {M : ℕ} {q : ℕ → ℝ} {A k Y l u : ℝ}
    (hA : 0 ≤ A) (hY : 0 < Y) (hYl : Y ≤ l) (hlu : l < u) (hlen : u - l ≤ 1)
    (hknots : ∀ n ∈ Finset.Ioc 0 M, (n : ℝ) ∈ Ioo l u → q n = 0) :
    let f := centeredRamp M q A k
    let C := ∫ x in l..u, positiveDensity (chord f l u) x
    C ≤ (∫ x in l..u, positiveDensity f x) ∧
    (∫ x in l..u, positiveDensity f x) ≤
      C + A / (4 * Y) * (l ^ (-(1 / 2) : ℝ) - u ^ (-(1 / 2) : ℝ)) := by
  let f := centeredRamp M q A k
  let c := chord f l u
  have hl := hY.trans_le hYl
  have hf := intervalIntegrable_density (continuous_centeredRamp M q A k) hl hlu.le
  have hc : IntervalIntegrable (positiveDensity c) volume l u := by
    apply intervalIntegrable_density _ hl hlu.le
    change Continuous (fun x : ℝ => (u - x) / (u - l) * f l + (x - l) / (u - l) * f u)
    fun_prop
  have hw : IntervalIntegrable (fun x => (A / (8 * Y)) * weight x) volume l u :=
    (continuousOn_const.mul (continuousOn_weight hl)).intervalIntegrable_of_Icc hlu.le
  change (∫ x in l..u, positiveDensity c x) ≤ (∫ x in l..u, positiveDensity f x) ∧
    (∫ x in l..u, positiveDensity f x) ≤ (∫ x in l..u, positiveDensity c x) +
      A / (4 * Y) * (l ^ (-(1 / 2) : ℝ) - u ^ (-(1 / 2) : ℝ))
  constructor
  · exact intervalIntegral.integral_mono_on hlu.le hc hf fun x hx =>
      (centeredRamp_density_bounds hA hY hYl hlu hlen hx hknots).1
  · calc
      _ ≤ ∫ x in l..u, positiveDensity c x + (A / (8 * Y)) * weight x :=
        intervalIntegral.integral_mono_on hlu.le hf (hc.add hw) fun x hx =>
          (centeredRamp_density_bounds hA hY hYl hlu hlen hx hknots).2
      _ = _ := by
        rw [intervalIntegral.integral_add hc hw, intervalIntegral.integral_const_mul,
          integral_weight hl hlu.le]
        field_simp [hY.ne'] <;> ring

/-- Finite sum of the weighted positive-part integrals of the endpoint chords. -/
def chordIntegralSum (f : ℝ → ℝ) (p : ℕ → ℝ) (J : ℕ) : ℝ :=
  ∑ j ∈ Finset.range J, ∫ x in p j..p (j + 1), positiveDensity (chord f (p j) (p (j + 1))) x

private theorem sum_inverse_root_sub (p : ℕ → ℝ) (J : ℕ) :
    (∑ j ∈ Finset.range J, ((p j) ^ (-(1 / 2) : ℝ) - (p (j + 1)) ^ (-(1 / 2) : ℝ))) =
      (p 0) ^ (-(1 / 2) : ℝ) - (p J) ^ (-(1 / 2) : ℝ) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- A partition certificate bounds the entire finite-window integral. Each cell
has length at most one and every interior coefficient on it vanishes. -/
private theorem centeredRamp_partition_integral_bounds {M J : ℕ} {q : ℕ → ℝ} {A k : ℝ}
    (p : ℕ → ℝ) (hA : 0 ≤ A) (hY : 0 < p 0)
    (hstep : ∀ j < J, p j < p (j + 1))
    (hlen : ∀ j < J, p (j + 1) - p j ≤ 1)
    (hknots : ∀ j < J, ∀ n ∈ Finset.Ioc 0 M, (n : ℝ) ∈ Ioo (p j) (p (j + 1)) → q n = 0) :
    let f := centeredRamp M q A k
    let C := chordIntegralSum f p J
    C ≤ (∫ x in p 0..p J, positiveDensity f x) ∧
    (∫ x in p 0..p J, positiveDensity f x) ≤
      C + A / (4 * p 0) * ((p 0) ^ (-(1 / 2) : ℝ) - (p J) ^ (-(1 / 2) : ℝ)) ∧
    (∫ x in p 0..p J, positiveDensity f x) ≤ C + A / (4 * (p 0) ^ (3 / 2 : ℝ)) := by
  let f := centeredRamp M q A k
  have hp : ∀ j ≤ J, p 0 ≤ p j := by
    intro j
    induction j with
    | zero => exact fun _ => le_rfl
    | succ j ih =>
      intro hj
      have hj' : j < J := by omega
      exact (ih hj'.le).trans (hstep j hj').le
  have hcell (j : ℕ) (hj : j < J) :=
    centeredRamp_cell_integral_bounds (k := k) hA hY (hp j hj.le)
      (hstep j hj) (hlen j hj) (hknots j hj)
  have hadd :
      (∑ j ∈ Finset.range J, ∫ x in p j..p (j + 1), positiveDensity f x) =
        ∫ x in p 0..p J, positiveDensity f x := by
    apply intervalIntegral.sum_integral_adjacent_intervals
    intro j hj
    exact intervalIntegrable_density (continuous_centeredRamp M q A k)
      (hY.trans_le (hp j hj.le)) (hstep j hj).le
  have hlo : chordIntegralSum f p J ≤ ∫ x in p 0..p J, positiveDensity f x := by
    rw [← hadd]
    exact Finset.sum_le_sum (fun j hj => (hcell j (Finset.mem_range.mp hj)).1)
  have hhi : (∫ x in p 0..p J, positiveDensity f x) ≤
      chordIntegralSum f p J +
        A / (4 * p 0) * ((p 0) ^ (-(1 / 2) : ℝ) - (p J) ^ (-(1 / 2) : ℝ)) := by
    rw [← hadd, chordIntegralSum, ← sum_inverse_root_sub p J, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j hj => (hcell j (Finset.mem_range.mp hj)).2)
  refine ⟨hlo, hhi, hhi.trans ?_⟩
  apply add_le_add_right
  calc
    _ ≤ A / (4 * p 0) * (p 0) ^ (-(1 / 2) : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (sub_le_self _ (Real.rpow_nonneg (hY.le.trans (hp J le_rfl)) _)) (by positivity)
    _ = A / (4 * (p 0) ^ (3 / 2 : ℝ)) := by
      rw [Real.rpow_neg hY.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
        Real.rpow_add hY, Real.rpow_one]
      have hroot : 0 < (p 0) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hY _
      field_simp [hY.ne', hroot.ne'] <;> ring

/-- Taking a fixed cutoff gives exactly the inclusive moving-floor ramp when the
window endpoint lies below the cutoff. This includes integer endpoints. -/
private theorem centeredRamp_eq_moving_floor {M : ℕ} {q : ℕ → ℝ} {A k x : ℝ}
    (hx : ⌊x⌋₊ ≤ M) :
    centeredRamp M q A k x = centeredRamp ⌊x⌋₊ q A k x := by
  have hsum :
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, q n * max (x / (n : ℝ) - 1) 0) =
        ∑ n ∈ Finset.Ioc 0 M, q n * max (x / (n : ℝ) - 1) 0 := by
    apply Finset.sum_subset (Finset.Ioc_subset_Ioc_right hx)
    intro n hn hn'
    have hlt : ⌊x⌋₊ < n :=
      lt_of_not_ge fun h => hn' (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, h⟩)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Ioc.mp hn).1
    have hnx : x ≤ (n : ℝ) := (Nat.lt_of_floor_lt hlt).le
    rw [max_eq_right (sub_nonpos.mpr ((div_le_one hn0).mpr hnx)), mul_zero]
  unfold centeredRamp
  rw [hsum]

/-- The endpoints and all interior integers, in increasing order on the window. -/
def integerWindowGrid (Y H : ℝ) (j : ℕ) : ℝ :=
  max Y (min H ((⌊Y⌋₊ + j : ℕ) : ℝ))

private theorem integerWindowGrid_endpoints {Y H : ℝ} (hY : 0 < Y) (hYH : Y < H) :
    integerWindowGrid Y H 0 = Y ∧
      integerWindowGrid Y H (⌈H⌉₊ - ⌊Y⌋₊) = H := by
  have hceil : ⌊Y⌋₊ ≤ ⌈H⌉₊ := by
    exact_mod_cast (Nat.floor_le hY.le).trans (hYH.le.trans (Nat.le_ceil H))
  constructor
  · exact max_eq_left ((min_le_right _ _).trans (by simpa using Nat.floor_le hY.le))
  · have hsum : ⌊Y⌋₊ + (⌈H⌉₊ - ⌊Y⌋₊) = ⌈H⌉₊ := by omega
    unfold integerWindowGrid
    rw [hsum, min_eq_left (Nat.le_ceil H), max_eq_right hYH.le]

private theorem integerWindowGrid_cell {Y H : ℝ} (hYH : Y < H) {j : ℕ}
    (hj : j < ⌈H⌉₊ - ⌊Y⌋₊) :
    let l := integerWindowGrid Y H j
    let u := integerWindowGrid Y H (j + 1)
    l < u ∧ u - l ≤ 1 ∧ ∀ n : ℕ, (n : ℝ) ∉ Ioo l u := by
  have hjH : ⌊Y⌋₊ + j < ⌈H⌉₊ := by omega
  let a : ℝ := ((⌊Y⌋₊ + j : ℕ) : ℝ)
  have haH : a < H := Nat.lt_ceil.mp hjH
  have hYa : Y < a + 1 := by
    have h : (⌊Y⌋₊ : ℝ) ≤ a := by dsimp only [a]; exact_mod_cast Nat.le_add_right _ _
    linarith only [Nat.lt_floor_add_one Y, h]
  have hnext : ((⌊Y⌋₊ + (j + 1) : ℕ) : ℝ) = a + 1 := by
    simp [a, Nat.cast_add, add_assoc]
  let b := min H (a + 1)
  have hYb : Y < b := lt_min hYH hYa
  have hab : a < b := lt_min haH (by linarith)
  have hl : integerWindowGrid Y H j = max Y a := by
    change max Y (min H a) = max Y a
    rw [min_eq_right haH.le]
  have hu : integerWindowGrid Y H (j + 1) = b := by
    unfold integerWindowGrid
    rw [hnext]
    exact max_eq_right hYb.le
  dsimp only
  rw [hl, hu]
  have hupper : b ≤ a + 1 := min_le_right _ _
  have hlower : a ≤ max Y a := le_max_right _ _
  refine ⟨max_lt hYb hab, ?_, ?_⟩
  · linarith only [hupper, hlower]
  · intro n hn
    have hleft : a < (n : ℝ) := hlower.trans_lt hn.1
    have hright : (n : ℝ) < a + 1 := hn.2.trans_le hupper
    have h0 : ⌊Y⌋₊ + j < n := by
      dsimp only [a] at hleft
      exact_mod_cast hleft
    have h1 : n < ⌊Y⌋₊ + j + 1 := by
      dsimp only [a] at hright
      exact_mod_cast hright
    omega

/-- The finite chord integral over the endpoints and all interior integers. -/
def integerChordIntegralSum (f : ℝ → ℝ) (Y H : ℝ) : ℝ :=
  chordIntegralSum f (integerWindowGrid Y H) (⌈H⌉₊ - ⌊Y⌋₊)

/-- On an arbitrary positive window, the explicit integer grid gives a
two-sided certificate for the weighted positive part, without a zero-line hypothesis. -/
private theorem centeredRamp_integer_window_bounds {M : ℕ} {q : ℕ → ℝ} {A k Y H : ℝ}
    (hA : 0 ≤ A) (hY : 0 < Y) (hYH : Y < H) :
    let f := centeredRamp M q A k
    let Q := integerChordIntegralSum f Y H
    Q ≤ (∫ x in Y..H, positiveDensity f x) ∧
      (∫ x in Y..H, positiveDensity f x) ≤
        Q + A / (4 * Y) * (Y ^ (-(1 / 2) : ℝ) - H ^ (-(1 / 2) : ℝ)) ∧
      (∫ x in Y..H, positiveDensity f x) ≤ Q + A / (4 * Y ^ (3 / 2 : ℝ)) := by
  obtain ⟨h0, hJ⟩ := integerWindowGrid_endpoints hY hYH
  have hY' : 0 < integerWindowGrid Y H 0 := h0.symm ▸ hY
  have h := centeredRamp_partition_integral_bounds (M := M) (q := q) (k := k)
    (J := ⌈H⌉₊ - ⌊Y⌋₊) (integerWindowGrid Y H) hA hY'
    (fun j hj => (integerWindowGrid_cell hYH hj).1)
    (fun j hj => (integerWindowGrid_cell hYH hj).2.1)
    (fun j hj n _ hn => ((integerWindowGrid_cell hYH hj).2.2 n hn).elim)
  dsimp only at h ⊢
  rw [h0, hJ] at h
  exact h

end DirichletPositiveWindowChord

open D5.S3.Arith.Robin.CompleteMertensPeak (U)
open D5.S3.CharacterSums.DirichletRampEndpoint (characterRamp gChi)
open D5.S3.Weil.Mertens.IntegratedExplicit
  (mangoldtRamp mangoldtPart mangoldtPart_eq_range U_eq_complete_ramps)
open DirichletPositiveWindowChord

namespace D5.S3.CharacterSums.DirichletJointPositiveWindow

/-- Combine the complete zeta ramp with a nonprincipal character ramp. -/
def jointRamp {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b x : ℝ) : ℝ :=
  a * U x + b * (gChi χ x).re

private def jointCoefficient {N : ℕ} (χ : DirichletCharacter ℂ N) (a b : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (a + b * (χ (n : ZMod N)).re)

private def jointCenter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a b : ℝ) : ℝ :=
  a * (1 + Real.eulerMascheroniConstant) + b * (deriv χ.LFunction 1 / χ.LFunction 1).re

private theorem centeredRamp_eq_jointRamp {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (a b : ℝ) {M : ℕ} {x : ℝ} (hx : 0 ≤ x) (hM : ⌊x⌋₊ ≤ M) :
    centeredRamp M (jointCoefficient χ a b) a (jointCenter χ a b) x = jointRamp χ a b x := by
  rw [centeredRamp_eq_moving_floor hM]
  have hrange : Finset.range (⌊x⌋₊ + 1) = insert 0 (Finset.Ioc 0 ⌊x⌋₊) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hpart : mangoldtPart x = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x := by
    rw [mangoldtPart_eq_range hx (N := ⌊x⌋₊ + 1) (by simpa using Nat.lt_floor_add_one x), hrange,
      Finset.sum_insert (by simp)]
    simp [mangoldtRamp]
  have hχre : (gChi χ x).re =
      (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x * (χ (n : ZMod N)).re) +
        x * (deriv χ.LFunction 1 / χ.LFunction 1).re := by
    simp only [gChi, ite_eq_right hχ, characterRamp, Complex.add_re, Complex.re_sum,
      Complex.re_ofReal_mul]
  have hsum : a * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x) +
      b * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, mangoldtRamp n x * (χ (n : ZMod N)).re) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, jointCoefficient χ a b n * max (x / (n : ℝ) - 1) 0 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold mangoldtRamp jointCoefficient
    ring
  rw [jointRamp, U_eq_complete_ramps hx, hpart, hχre]
  unfold centeredRamp jointCenter
  rw [← hsum]
  ring

/-- The finite integer-grid mass certifies the weighted positive part of the
actual zeta and nonprincipal-character ramp on every positive interval. -/
theorem jointRamp_positive_window_bounds {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {a b Y H : ℝ} (ha : 0 ≤ a) (hY : 0 < Y) (hYH : Y < H) :
    let g := jointRamp χ a b
    let Q := integerChordIntegralSum g Y H
    Q ≤ (∫ x in Y..H, positiveDensity g x) ∧
      (∫ x in Y..H, positiveDensity g x) ≤
        Q + a / (4 * Y) * (Y ^ (-(1 / 2) : ℝ) - H ^ (-(1 / 2) : ℝ)) ∧
      (∫ x in Y..H, positiveDensity g x) ≤ Q + a / (4 * Y ^ (3 / 2 : ℝ)) := by
  let f := centeredRamp ⌊H⌋₊ (jointCoefficient χ a b) a (jointCenter χ a b)
  let g := jointRamp χ a b
  have heq {x : ℝ} (hx : x ∈ Icc Y H) : f x = g x :=
    centeredRamp_eq_jointRamp hχ a b (hY.le.trans hx.1) (Nat.floor_mono hx.2)
  have hI : (∫ x in Y..H, positiveDensity f x) = ∫ x in Y..H, positiveDensity g x := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le hYH.le] at hx
    rw [positiveDensity, positiveDensity, heq hx]
  have hgrid (j : ℕ) : integerWindowGrid Y H j ∈ Icc Y H :=
    ⟨le_max_left _ _, max_le hYH.le (min_le_left _ _)⟩
  have hQ : integerChordIntegralSum f Y H = integerChordIntegralSum g Y H := by
    unfold integerChordIntegralSum chordIntegralSum
    apply Finset.sum_congr rfl
    intro j _
    refine intervalIntegral.integral_congr fun x _ => ?_
    unfold positiveDensity chord
    rw [heq (hgrid j), heq (hgrid (j + 1))]
  have h := centeredRamp_integer_window_bounds (M := ⌊H⌋₊) (q := jointCoefficient χ a b)
    (k := jointCenter χ a b) ha hY hYH
  dsimp only at h ⊢
  change integerChordIntegralSum f Y H ≤ (∫ x in Y..H, positiveDensity f x) ∧
    (∫ x in Y..H, positiveDensity f x) ≤ integerChordIntegralSum f Y H + _ ∧
    (∫ x in Y..H, positiveDensity f x) ≤ integerChordIntegralSum f Y H + _ at h
  rw [hI, hQ] at h
  exact h

/-- Subpower control on arbitrarily late power windows can be measured by
the finite positive chord masses. The two estimates use the same exponent threshold. -/
theorem jointRamp_subpower_windows_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {a b δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) :
    let g := jointRamp χ a b
    (∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 2 Y₀ ≤ Y ∧
      (∫ x in Y..Y ^ (1 + δ), positiveDensity g x) ≤ Y ^ η) ↔
    (∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, max 2 Y₀ ≤ Y ∧
      integerChordIntegralSum g Y (Y ^ (1 + δ)) ≤ Y ^ η) := by
  have hwindow {Y : ℝ} (hY : 2 ≤ Y) : Y < Y ^ (1 + δ) := by
    have hY1 : 1 < Y := (by norm_num : (1 : ℝ) < 2).trans_le hY
    have hYpos : 0 < Y := zero_lt_one.trans hY1
    rw [Real.rpow_add hYpos, Real.rpow_one]
    exact lt_mul_of_one_lt_right hYpos (Real.one_lt_rpow hY1 hδ)
  constructor
  · intro h η hη Y₀
    obtain ⟨Y, hY, hI⟩ := h η hη Y₀
    have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
    have hYpos : 0 < Y := (by norm_num : (0 : ℝ) < 2).trans_le hY2
    exact ⟨Y, hY, (jointRamp_positive_window_bounds hχ ha hYpos (hwindow hY2)).1.trans hI⟩
  · intro h η hη Y₀
    have hhalf : 0 < η / 2 := half_pos hη
    obtain ⟨T, hT⟩ := eventually_atTop.mp
      ((tendsto_rpow_atTop hhalf).eventually_ge_atTop (max 2 (a / 4)))
    obtain ⟨Y, hY, hQ⟩ := h (η / 2) hhalf (max Y₀ T)
    have hY2 : 2 ≤ Y := (le_max_left _ _).trans hY
    have hY0 : Y₀ ≤ Y := (le_max_left Y₀ T).trans ((le_max_right _ _).trans hY)
    have hYT : T ≤ Y := (le_max_right Y₀ T).trans ((le_max_right _ _).trans hY)
    have hYpos : 0 < Y := (by norm_num : (0 : ℝ) < 2).trans_le hY2
    have hM := hT Y hYT
    have hE : a / (4 * Y ^ (3 / 2 : ℝ)) ≤ a / 4 := by
      have hPow : 1 ≤ Y ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_zero Y]
        exact Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans hY2)
          (by norm_num)
      exact div_le_div_of_nonneg_left ha (by norm_num) (by linarith)
    have h₂ : 2 ≤ Y ^ (η / 2) := (le_max_left _ _).trans hM
    have hₐ : a / 4 ≤ Y ^ (η / 2) := (le_max_right _ _).trans hM
    refine ⟨Y, max_le hY2 hY0, ?_⟩
    calc
      _ ≤ _ := (jointRamp_positive_window_bounds hχ ha hYpos (hwindow hY2)).2.2
      _ ≤ Y ^ (η / 2) + Y ^ (η / 2) := add_le_add hQ (hE.trans hₐ)
      _ = 2 * Y ^ (η / 2) := by ring
      _ ≤ Y ^ (η / 2) * Y ^ (η / 2) :=
        mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg hYpos.le _)
      _ = Y ^ η := by rw [← Real.rpow_add hYpos, show η / 2 + η / 2 = η by ring]

end D5.S3.CharacterSums.DirichletJointPositiveWindow
