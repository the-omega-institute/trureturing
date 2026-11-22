/- GID: D5/S1/Words/Patterns/Separable/OccupiedMellinInterior
   generality: G
   mirror-B: D5/B/S1/Words/Patterns/Separable/OccupiedMellinInterior
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.MeanValue]
   utility: none
   digest: Quantitative lattice-to-integral comparison on regular Mellin blocks. -/

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Away from the two singularities, the exact regularized Mellin samples of
the occupation-kernel comparison admit an explicit uniform quadrature error. -/

namespace D5.S1.Words.Patterns.Separable.OccupiedMellinInterior

open Set

/-- Paired Mellin samples. The nonnegative shift is zero in the integral and
is `2 / n` at the finite lattice nodes. -/
noncomputable def sample (β a s : ℝ) : ℝ :=
  s ^ (-(3/2 : ℝ)) * ((a+(1+s))^(-β)+(a+|1 - s|)^(-β)-2*(a+1)^(-β))

private theorem rpow_bound {δ x p q : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : δ ≤ x) (hp : p ≤ 0) (hq : q ≤ p) : x ^ p ≤ δ ^ q :=
  (Real.rpow_le_rpow_of_nonpos hδ hx hp).trans
    (Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hq)

private theorem sample_derivative_at {β a s δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : δ ≤ s)
    (ht : δ ≤ |1 - s|) :
    ∃ L : ℝ, HasDerivAt (sample β a) L s ∧ |L| ≤ 8 * δ ^ (-(13 / 4:ℝ)) := by
  have hs0 : 0 < s := hδ.trans_le hs
  have hx0 : 0 < a + (1+s) := by linarith
  have hy0 : 0 < a + |1 - s| := by linarith
  have h1 : 0 < a + 1 := by linarith
  have hne : (1:ℝ)-s ≠ 0 := by
    intro h
    rw [h, abs_zero] at ht
    linarith
  let p := (a+(1+s)) ^ (-β)
  let q := (a+|1 - s|) ^ (-β)
  let c := (a+1) ^ (-β)
  let w := s ^ (-(3/2:ℝ))
  let wp := (-(3/2:ℝ)) * s ^ (-(3/2:ℝ)-1)
  let pp := (-β) * (a+(1+s)) ^ (-β-1)
  have hw : HasDerivAt (fun x : ℝ => x ^ (-(3/2:ℝ))) wp s :=
    Real.hasDerivAt_rpow_const (Or.inl hs0.ne')
  have hx : HasDerivAt (fun x : ℝ => a+(1+x)) 1 s := (hasDerivAt_id s).const_add 1 |>.const_add a
  have hp : HasDerivAt (fun x : ℝ => (a+(1+x)) ^ (-β)) pp s := by
    simpa only [pp, id_eq, one_mul] using hx.rpow_const (p := -β) (Or.inl hx0.ne')
  have hf : HasDerivAt (fun x : ℝ => 1-x) (-1) s := (hasDerivAt_id s).const_sub 1
  obtain ⟨ε, hε, he⟩ : ∃ ε : ℝ, |ε| = 1 ∧
      HasDerivAt (fun x : ℝ => a+|1-x|) ε s := by
    rcases lt_or_gt_of_ne hne with hn | hp
    · refine ⟨1, abs_one, ?_⟩
      simpa only [neg_mul, one_mul, neg_neg, Function.comp_def] using
        ((hasDerivAt_abs_neg hn).comp s hf).const_add a
    · refine ⟨-1, by norm_num, ?_⟩
      simpa only [one_mul, Function.comp_def] using
        ((hasDerivAt_abs_pos hp).comp s hf).const_add a
  let qp := ε * (-β) * (a+|1 - s|) ^ (-β-1)
  have hq : HasDerivAt (fun x : ℝ => (a+|1-x|) ^ (-β)) qp s :=
    he.rpow_const (Or.inl hy0.ne')
  refine ⟨wp * (p+q-2*c) + w * (pp+qp), ?_, ?_⟩
  · exact hw.mul ((hp.add hq).sub_const (2*c))
  have hp0 : 0 ≤ p := Real.rpow_nonneg hx0.le _
  have hq0 : 0 ≤ q := Real.rpow_nonneg hy0.le _
  have hc0 : 0 ≤ c := Real.rpow_nonneg h1.le _
  have hw0 : 0 ≤ w := Real.rpow_nonneg hs0.le _
  have hpB : p ≤ δ ^ (-(3 / 4:ℝ)) :=
    rpow_bound hδ hδ1 (by linarith : δ ≤ a+(1+s)) (by linarith) (by linarith)
  have hqB : q ≤ δ ^ (-(3 / 4:ℝ)) :=
    rpow_bound hδ hδ1 (by linarith : δ ≤ a+|1 - s|) (by linarith) (by linarith)
  have hcB : c ≤ δ ^ (-(3 / 4:ℝ)) :=
    rpow_bound hδ hδ1 (by linarith : δ ≤ a+1) (by linarith) (by linarith)
  have hh : |p+q-2*c| ≤ 4 * δ ^ (-(3 / 4:ℝ)) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hwb : w ≤ δ ^ (-(3/2:ℝ)) := rpow_bound hδ hδ1 hs (by norm_num) le_rfl
  have hwp : |wp| ≤ (3/2) * δ ^ (-(5/2:ℝ)) := by
    dsimp only [wp]
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hs0.le _),
      abs_of_nonpos (show -(3 / 2 : ℝ) ≤ 0 by norm_num), neg_neg]
    have hb : s ^ (-(3/2:ℝ)-1) ≤ δ ^ (-(5/2:ℝ)) :=
      rpow_bound hδ hδ1 hs (by norm_num) (by norm_num)
    exact mul_le_mul_of_nonneg_left hb (by norm_num)
  have hpp : |pp| ≤ δ ^ (-(7/4:ℝ)) := by
    dsimp only [pp]
    rw [abs_mul, abs_neg, abs_of_nonneg hβ, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
    exact (mul_le_mul (show β ≤ 1 by linarith)
      (rpow_bound hδ hδ1 (by linarith) (by linarith) (by linarith))
      (Real.rpow_nonneg hx0.le _) zero_le_one).trans_eq (one_mul _)
  have hqp : |qp| ≤ δ ^ (-(7/4:ℝ)) := by
    dsimp only [qp]
    rw [abs_mul, abs_mul, hε, one_mul, abs_neg, abs_of_nonneg hβ,
      abs_of_nonneg (Real.rpow_nonneg hy0.le _)]
    exact (mul_le_mul (show β ≤ 1 by linarith)
      (rpow_bound hδ hδ1 (by linarith) (by linarith) (by linarith))
      (Real.rpow_nonneg hy0.le _) zero_le_one).trans_eq (one_mul _)
  have hder : |pp+qp| ≤ 2 * δ ^ (-(7/4:ℝ)) := (abs_add_le _ _).trans (by linarith)
  calc
    _ ≤ |wp| * |p+q-2*c| + w * |pp+qp| := by
      simpa only [abs_mul, abs_of_nonneg hw0] using abs_add_le (wp*(p+q-2*c)) (w*(pp+qp))
    _ ≤ ((3/2) * δ ^ (-(5/2:ℝ))) * (4 * δ ^ (-(3 / 4:ℝ))) +
        δ ^ (-(3/2:ℝ)) * (2 * δ ^ (-(7/4:ℝ))) := by
      exact add_le_add
        (mul_le_mul hwp hh (abs_nonneg _) (by positivity))
        (mul_le_mul hwb hder (abs_nonneg _) (by positivity))
    _ = _ := by
      ring_nf
      rw [← Real.rpow_add hδ, ← Real.rpow_add hδ]
      norm_num
      ring

/-- The ordinary derivative bound is uniform over the exponent and the
nonnegative regularizing shift. Both bases must stay at least δ from zero. -/
private theorem sample_deriv_le {β a s δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : δ ≤ s) (ht : δ ≤ |1 - s|) :
    |deriv (sample β a) s| ≤ 8 * δ ^ (-(13 / 4:ℝ)) := by
  obtain ⟨L, hL, h⟩ := sample_derivative_at hβ hβ' ha hδ hδ1 hs ht
  rwa [hL.deriv]

/-- Mean value bound on any interval on one side of the singularity. The
segment need not satisfy any additional upper cutoff. -/
private theorem sample_lipschitz_interval {β a δ u v x y : ℝ}
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (hside : v ≤ 1 - δ ∨ 1 + δ ≤ u) (hx : x ∈ Icc u v) (hy : y ∈ Icc u v) :
    |sample β a y - sample β a x| ≤ (8 * δ ^ (-(13 / 4:ℝ))) * |y-x| := by
  have hg : ∀ t ∈ Icc u v, δ ≤ t ∧ δ ≤ |1-t| := by
    intro t ht
    refine ⟨hu.trans ht.1, ?_⟩
    rcases hside with hl | hr
    · exact (show δ ≤ 1-t by linarith [ht.2]).trans (le_abs_self _)
    · exact (show δ ≤ -(1-t) by linarith [ht.1]).trans (neg_le_abs _)
  have hd : ∀ t ∈ Icc u v, DifferentiableAt ℝ (sample β a) t := by
    intro t ht
    obtain ⟨L, hL, _⟩ := sample_derivative_at hβ hβ' ha hδ hδ1 (hg t ht).1 (hg t ht).2
    exact hL.differentiableAt
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le hd
    (fun t ht => by
      rw [Real.norm_eq_abs]
      exact sample_deriv_le hβ hβ' ha hδ hδ1 (hg t ht).1 (hg t ht).2)
    (convex_Icc u v) hx hy

open scoped BigOperators

private theorem sample_intervalIntegrable {β a δ u v : ℝ}
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (huv : u ≤ v) (hside : v ≤ 1 - δ ∨ 1 + δ ≤ u) :
    IntervalIntegrable (sample β a) MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le huv]
  intro x hx
  have ht : δ ≤ |1-x| := by
    rcases hside with hl | hr
    · exact (show δ ≤ 1-x by linarith [hx.2]).trans (le_abs_self _)
    · exact (show δ ≤ -(1-x) by linarith [hx.1]).trans (neg_le_abs _)
  obtain ⟨L, hL, _⟩ := sample_derivative_at hβ hβ' ha hδ hδ1 (hu.trans hx.1) ht
  exact hL.continuousAt.continuousWithinAt

/-- The exact left-sample cell error, for either the shifted or unshifted profile. -/
private theorem sample_cell_error {β a δ u v : ℝ}
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (huv : u ≤ v) (hside : v ≤ 1 - δ ∨ 1 + δ ≤ u) :
    |(∫ t in u..v, sample β a t) - (v-u) * sample β a u| ≤
      (8 * δ ^ (-(13 / 4:ℝ))) * (v-u)^2 := by
  let K := 8 * δ ^ (-(13 / 4:ℝ))
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hI := sample_intervalIntegrable hβ hβ' ha hδ hδ1 hu huv hside
  have hc : IntervalIntegrable (fun _ : ℝ => sample β a u) MeasureTheory.volume u v :=
    intervalIntegrable_const
  have heq := intervalIntegral.integral_sub hI hc
  rw [intervalIntegral.integral_const, smul_eq_mul] at heq
  rw [← heq]
  have hb : ‖∫ t in u..v, sample β a t - sample β a u‖ ≤ K * (v-u) * |v-u| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro x hx
    rw [uIoc_of_le huv] at hx
    rw [Real.norm_eq_abs]
    apply (sample_lipschitz_interval hβ hβ' ha hδ hδ1 hu hside
      (left_mem_Icc.mpr huv) ⟨hx.1.le, hx.2⟩).trans
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1.le)]
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 _) hK
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr huv)] at hb
  exact hb.trans_eq (by dsimp only [K]; ring)

/-- Uniform grid on an interval lying wholly on one side of 1. This result
does not handle cells that intersect a cutoff endpoint. -/
private theorem sample_uniform_mesh_error {β a δ u h : ℝ} (N : ℕ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (hh : 0 ≤ h) (hside : u + N * h ≤ 1 - δ ∨ 1 + δ ≤ u) :
    |(∫ t in u..(u + N * h), sample β a t) -
        ∑ i ∈ Finset.range N, h * sample β a (u + i*h)| ≤
      (8 * δ ^ (-(13 / 4:ℝ))) * ((N : ℝ) * h^2) := by
  let z (i : ℕ) := u + i*h
  let K := 8 * δ ^ (-(13 / 4:ℝ))
  have hmono : Monotone z := by
    intro i j hij
    have hcast : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcast hh)
  have hend (i : ℕ) (hi : i < N) :
      δ ≤ z i ∧ z i ≤ z (i+1) ∧ (z (i+1) ≤ 1 - δ ∨ 1 + δ ≤ z i) := by
    have hz : u ≤ z i := le_add_of_nonneg_right (by positivity)
    refine ⟨hu.trans hz, hmono (Nat.le_succ i), ?_⟩
    rcases hside with hl | hr
    · exact Or.inl ((hmono (Nat.succ_le_of_lt hi)).trans hl)
    · exact Or.inr (hr.trans hz)
  have hf (i : ℕ) (hi : i < N) :
      IntervalIntegrable (sample β a) MeasureTheory.volume (z i) (z (i+1)) := by
    obtain ⟨hlo, hle, hcut⟩ := hend i hi
    exact sample_intervalIntegrable hβ hβ' ha hδ hδ1 hlo hle hcut
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (a := z) hf
  have hz0 : z 0 = u := by simp [z]
  change |(∫ t in u..z N, sample β a t) -
        ∑ i ∈ Finset.range N, h * sample β a (z i)| ≤ K * ((N : ℝ) * h^2)
  rw [← hz0, ← hsum, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ Finset.range N, K * h^2 := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨hlo, hle, hcut⟩ := hend i (Finset.mem_range.mp hi)
      have hd : z (i+1) - z i = h := by simp only [z, Nat.cast_succ]; ring
      simpa only [hd] using (sample_cell_error hβ hβ' ha hδ hδ1 hlo hle hcut)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- A regular interval of length at most δ⁻¹ has total mesh error at most
(8δ^{-17/4}h), with no dependence on β or the shift. -/
private theorem sample_uniform_mesh_error_cutoff {β a δ u h : ℝ} (N : ℕ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (hh : 0 ≤ h) (hlen : (N : ℝ) * h ≤ δ⁻¹)
    (hside : u + N * h ≤ 1 - δ ∨ 1 + δ ≤ u) :
    |(∫ t in u..(u + N * h), sample β a t) -
        ∑ i ∈ Finset.range N, h * sample β a (u + i*h)| ≤
      (8 * δ ^ (-(17/4:ℝ))) * h := by
  apply (sample_uniform_mesh_error N hβ hβ' ha hδ hδ1 hu hh hside).trans
  calc
    _ = (8 * δ ^ (-(13 / 4:ℝ))) * ((N : ℝ) * h) * h := by ring
    _ ≤ (8 * δ ^ (-(13 / 4:ℝ))) * δ⁻¹ * h := by gcongr
    _ = _ := by
      rw [show δ⁻¹ = δ ^ (-(1:ℝ)) from (Real.rpow_neg_one _).symm,
        mul_assoc (8:ℝ), ← Real.rpow_add hδ]
      norm_num

private theorem power_shift_bound {x a β δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : δ ≤ x) :
    |(a+x)^(-β) - x^(-β)| ≤ δ ^ (-(7/4:ℝ)) * a := by
  have hd (t : ℝ) (ht : t ∈ Icc x (a+x)) :
      HasDerivAt (fun w : ℝ => w ^ (-β)) ((-β) * t ^ (-β-1)) t :=
    Real.hasDerivAt_rpow_const (Or.inl (hδ.trans_le (hx.trans ht.1)).ne')
  have hab : x ≤ a+x := by linarith
  have hv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (C := δ ^ (-(7/4:ℝ)))
    (fun t ht => (hd t ht).hasDerivWithinAt)
    (fun t ht => by
      rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hβ,
        abs_of_nonneg (Real.rpow_nonneg (hδ.le.trans (hx.trans ht.1)) _)]
      exact (mul_le_mul (show β ≤ 1 by linarith)
        (rpow_bound hδ hδ1 (hx.trans ht.1) (by linarith) (by linarith))
        (Real.rpow_nonneg (hδ.le.trans (hx.trans ht.1)) _) zero_le_one).trans_eq (one_mul _))
    (convex_Icc x (a+x)) (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)
  simpa only [Real.norm_eq_abs, add_sub_cancel_right, abs_of_nonneg ha] using hv

/-- On a regular cell the difference between exact regularization and the
unshifted profile is linear in the shift. -/
private theorem sample_shift_error {β a s δ : ℝ} (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4)
    (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : δ ≤ s) (ht : δ ≤ |1 - s|) :
    |sample β a s - sample β 0 s| ≤ (4 * δ ^ (-(13 / 4:ℝ))) * a := by
  have hp := power_shift_bound hβ hβ' ha hδ hδ1 (show δ ≤ 1+s by linarith)
  have hq := power_shift_bound hβ hβ' ha hδ hδ1 ht
  have hc := power_shift_bound hβ hβ' ha hδ hδ1 hδ1
  let p := (a+(1+s))^(-β)-(1+s)^(-β)
  let q := (a+|1 - s|)^(-β)-|1 - s|^(-β)
  let c := (a+1)^(-β)-(1:ℝ)^(-β)
  let w := s ^ (-(3/2:ℝ))
  have hw : 0 ≤ w := Real.rpow_nonneg (hδ.le.trans hs) _
  have hwb : w ≤ δ ^ (-(3/2:ℝ)) := rpow_bound hδ hδ1 hs (by norm_num) le_rfl
  have hab : |p+q-2*c| ≤ 4 * δ ^ (-(7/4:ℝ)) * a := by
    calc
      _ ≤ |p+q| + |2*c| := by
        simpa only [abs_neg, sub_eq_add_neg] using abs_add_le (p+q) (-(2*c))
      _ ≤ (|p| + |q|) + 2*|c| := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
        exact add_le_add (abs_add_le _ _) le_rfl
      _ ≤ _ := by
        dsimp only [p, q, c]
        linarith only [hp, hq, hc]
  have he : sample β a s - sample β 0 s = w * (p+q-2*c) := by
    simp only [sample, w, p, q, c, zero_add]
    ring
  rw [he, abs_mul, abs_of_nonneg hw]
  calc
    _ ≤ δ ^ (-(3/2:ℝ)) * (4 * δ ^ (-(7/4:ℝ)) * a) :=
      mul_le_mul hwb hab (abs_nonneg _) (by positivity)
    _ = _ := by
      have heq : δ ^ (-(3/2:ℝ)) * δ ^ (-(7/4:ℝ)) = δ ^ (-(13 / 4:ℝ)) := by
        rw [← Real.rpow_add hδ]
        norm_num
      calc
        _ = 4 * (δ ^ (-(3/2:ℝ)) * δ ^ (-(7/4:ℝ))) * a := by ring
        _ = _ := by rw [heq]

/-- The exact shifted left samples, compared with the unshifted integral on
a regular uniform grid. The application uses h = 1/n and a = 2h. -/
private theorem shifted_mesh_vs_unshifted {β a δ u h : ℝ} (N : ℕ)
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (ha : 0 ≤ a) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hu : δ ≤ u) (hh : 0 ≤ h) (hlen : (N : ℝ) * h ≤ δ⁻¹)
    (hside : u + N * h ≤ 1 - δ ∨ 1 + δ ≤ u) :
    |(∫ t in u..(u + N * h), sample β 0 t) -
        ∑ i ∈ Finset.range N, h * sample β a (u + i*h)| ≤
      δ ^ (-(17/4:ℝ)) * (8*h + 4*a) := by
  let f (r : ℝ) := ∑ i ∈ Finset.range N, h * sample β r (u + i*h)
  let I := ∫ t in u..(u + N * h), sample β 0 t
  have hI : |I - f 0| ≤ (8 * δ ^ (-(17/4:ℝ))) * h :=
    sample_uniform_mesh_error_cutoff N hβ hβ' le_rfl hδ hδ1 hu hh hlen hside
  have hS : |f 0 - f a| ≤ (4 * δ ^ (-(17/4:ℝ))) * a := by
    unfold f
    rw [← Finset.sum_sub_distrib]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    have hP : ∀ i ∈ Finset.range N,
        |h * sample β 0 (u + i*h) - h * sample β a (u + i*h)| ≤
          h * ((4 * δ ^ (-(13 / 4:ℝ))) * a) := by
      intro i hi
      let s := u + i*h
      have hl : u ≤ s := le_add_of_nonneg_right (by positivity)
      have hr : s ≤ u + N * h := by
        have hcast : (i : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hi).le
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcast hh)
      have hb : δ ≤ |1 - s| := by
        rcases hside with hleft | hright
        · exact (show δ ≤ 1-s by linarith).trans (le_abs_self _)
        · exact (show δ ≤ -(1-s) by linarith).trans (neg_le_abs _)
      have hE := sample_shift_error hβ hβ' ha hδ hδ1 (hu.trans hl) hb
      change |h * sample β 0 s - h * sample β a s| ≤ _
      rw [← mul_sub, abs_mul, abs_of_nonneg hh, abs_sub_comm]
      exact mul_le_mul_of_nonneg_left hE hh
    calc
      _ ≤ ∑ i ∈ Finset.range N, h * ((4 * δ ^ (-(13 / 4:ℝ))) * a) :=
        Finset.sum_le_sum hP
      _ = ((N : ℝ) * h) * ((4 * δ ^ (-(13 / 4:ℝ))) * a) := by
        simp [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ δ⁻¹ * ((4 * δ ^ (-(13 / 4:ℝ))) * a) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
      _ = _ := by
        have hpow : δ⁻¹ * δ ^ (-(13 / 4:ℝ)) = δ ^ (-(17/4:ℝ)) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]
          norm_num
        calc
          _ = (4 * (δ⁻¹ * δ ^ (-(13 / 4:ℝ)))) * a := by ring
          _ = _ := by rw [hpow]
  change |I - f a| ≤ _
  calc
    _ ≤ |I - f 0| + |f 0 - f a| := abs_sub_le _ _ _
    _ ≤ (8 * δ ^ (-(17/4:ℝ))) * h + (4 * δ ^ (-(17/4:ℝ))) * a := add_le_add hI hS
    _ = _ := by ring

/-- Uniform quadrature error for the exact grid with step `1 / n` and shift `2 / n`.
Both endpoints of every cell stay in one regular component. -/
theorem normalized_lattice_interior_error {β δ : ℝ} (n L N : ℕ) (hn : 0 < n)
    (hβ : 0 ≤ β) (hβ' : β ≤ 3 / 4) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hL : δ ≤ (L : ℝ) / n) (hlen : (N : ℝ) / n ≤ δ⁻¹)
    (hside : ((L + N : ℕ) : ℝ) / n ≤ 1 - δ ∨ 1 + δ ≤ (L : ℝ) / n) :
    |(∫ t in ((L:ℝ) / n)..(((L + N:ℕ):ℝ) / n), sample β 0 t) -
        ∑ i ∈ Finset.range N, (1/(n:ℝ)) * sample β (2/(n:ℝ)) (((L+i:ℕ):ℝ) / n)| ≤
      (16 * δ ^ (-(17/4:ℝ))) / n := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast hn
  have Hadd (i : ℕ) : (L : ℝ) / n + (i : ℝ)*(1/(n:ℝ)) = ((L+i:ℕ):ℝ) / n := by
    push_cast
    ring
  have hmul : (N : ℝ) * (1/(n:ℝ)) ≤ δ⁻¹ := by
    convert hlen using 1
    ring
  have hs : (L:ℝ) / n + (N : ℝ)*(1/(n:ℝ)) ≤ 1 - δ ∨ 1 + δ ≤ (L:ℝ) / n := by
    rwa [Hadd]
  have h := shifted_mesh_vs_unshifted (a := 2/(n:ℝ)) N hβ hβ'
    (by positivity) hδ hδ1 hL (by positivity) hmul hs
  simp only [Hadd] at h
  exact h.trans_eq (by ring)

end D5.S1.Words.Patterns.Separable.OccupiedMellinInterior
