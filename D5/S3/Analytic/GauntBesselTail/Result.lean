/- GID: D5/S3/Analytic/GauntBesselTail/Result
   generality: G
   mirror-B: D5/B/S3/Analytic/GauntBesselTail/Result
   mirror-E: none(waiver:external-open-problem-resolution)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Sqrt]
   utility: none
   digest: Squared-order convexity supplies the kernel comparison for Gaunt's Bessel tail bound. -/

/-
The utility classification is none: the statements concern arbitrary real
parameters and analytic integrals, rather than finite computations or instances.
The intended settlement is open-problem-resolution (#22457; Proved).
No settlement theorem is asserted by the definitions alone.
-/

import D5.S3.Analytic.GammaGammaNBU.Result
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Real Set MeasureTheory Filter
open scoped Topology
noncomputable section
namespace D5.S3.Analytic.GauntBesselTail.Result
open D5.S3.Analytic.GammaGammaNBU.Result (besselK)

def alpha (ν n : ℝ) : ℝ := ν+n-sqrt ((ν+n)^2-2*ν-1)
def alphaPrime (ν n : ℝ) : ℝ := ν+n+sqrt ((ν+n)^2-2*ν-1)
def tail (ν p x : ℝ) : ℝ := ∫ t in Ioi x, t^(-ν) * besselK p t

def claim : Prop :=
  (∀ n ν : ℝ, n < 1 → 1-n+sqrt (2*(1-n)) ≤ ν → ∀ x : ℝ, 0 < x →
    x^(-ν) * besselK (ν+n-alpha ν n) x < tail ν (ν+n) x) ∧
  (∀ n ν : ℝ, n < 1 → 1-n+sqrt (2*(1-n)) ≤ ν → ∀ β : ℝ,
    β ∉ ({alpha ν n, alphaPrime ν n} : Set ℝ) →
    (∀ x : ℝ, 0 < x → x^(-ν) * besselK (ν+n-β) x <
      x^(-ν) * besselK (ν+n-alpha ν n) x) ∨
    (∃ y : ℝ, 0 < y ∧ tail ν (ν+n) y < y^(-ν) * besselK (ν+n-β) y)) ∧
  (∀ ν x : ℝ, 0 < x → tail ν (ν+1) x = x^(-ν) * besselK ν x)

private lemma sinh_gap_pos {v : ℝ} (hv : 0 < v) :
    0 < v * cosh v - sinh v := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y * cosh y - sinh y)
      (x * sinh x) x := by
    convert ((hasDerivAt_id x).mul (hasDerivAt_cosh x)).sub (hasDerivAt_sinh x) using 1 <;> first | rfl | (try dsimp; ring)
  have hm : StrictMonoOn (fun y : ℝ => y * cosh y - sinh y) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0) (by fun_prop)
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact mul_pos hx (sinh_pos_iff.mpr hx)
  simpa using hm (show 0 ∈ Ici (0 : ℝ) by simp) hv.le hv

private lemma cosh_sqrt_deriv (u s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => cosh (u * sqrt s))
      (u / (2 * sqrt s) * sinh (u * sqrt s)) s := by
  convert (hasDerivAt_cosh (u * sqrt s)).comp s
    ((hasDerivAt_sqrt hs.ne').const_mul u) using 1
  · rfl
  · ring

private lemma cosh_sqrt_deriv2 (u s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun s : ℝ => u / (2 * sqrt s) * sinh (u * sqrt s))
      (u / (4 * (sqrt s)^3) * (u * sqrt s * cosh (u * sqrt s) - sinh (u * sqrt s))) s := by
  have hn := (sqrt_pos_of_pos hs).ne'
  convert ((hasDerivAt_const s u).div ((hasDerivAt_sqrt hs.ne').const_mul 2)
    (mul_ne_zero (by norm_num) hn)).mul
    ((hasDerivAt_sinh (u * sqrt s)).comp s ((hasDerivAt_sqrt hs.ne').const_mul u)) using 1
  · rfl
  · dsimp
    field_simp
    ring

private lemma squared_order_strictConvex {u : ℝ} (hu : 0 < u) :
    StrictConvexOn ℝ (Ici 0) (fun s : ℝ => cosh (u * sqrt s)) := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) (by fun_prop)
  intro s hs
  rw [interior_Ici] at hs
  have he : deriv (fun s : ℝ => cosh (u * sqrt s)) =ᶠ[𝓝 s]
      (fun s => u / (2 * sqrt s) * sinh (u * sqrt s)) := by
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact (cosh_sqrt_deriv u t ht).deriv
  rw [Function.iterate_succ_apply', Function.iterate_one, he.deriv_eq]
  rw [(cosh_sqrt_deriv2 u s hs).deriv]
  have hsqrt := sqrt_pos_of_pos hs
  exact mul_pos (div_pos hu (by positivity))
    (sinh_gap_pos (mul_pos hu (sqrt_pos_of_pos hs)))

private lemma cosh_sqrt_sq (u a : ℝ) (hu : 0 ≤ u) :
    cosh (u * sqrt (a^2)) = cosh (a*u) := by
  calc
    _ = cosh |u*a| := by rw [sqrt_sq_eq_abs, abs_mul, abs_of_nonneg hu]
    _ = _ := by rw [cosh_abs, mul_comm]

private lemma positive_order_kernel {u p q ν : ℝ} (hu : 0 < u)
    (hq : 0 < q) (hν : q < ν) (he : p^2 = q^2 + 2*ν + 1) :
    cosh (q*u) * cosh u + ν/q * sinh (q*u) * sinh u < cosh (p*u) := by
  have hab : (q-1)^2 < (q+1)^2 := by nlinarith
  have hbc : (q+1)^2 < p^2 := by nlinarith
  have hc := (squared_order_strictConvex hu).slope_strict_mono_adjacent
    (sq_nonneg (q-1)) (sq_nonneg p) hab hbc
  rw [cosh_sqrt_sq u (q+1) hu.le, cosh_sqrt_sq u (q-1) hu.le,
    cosh_sqrt_sq u p hu.le] at hc
  rw [add_mul, sub_mul, one_mul, cosh_add, cosh_sub] at hc
  have hc' := (div_lt_div_iff₀ (sub_pos.mpr hab) (sub_pos.mpr hbc)).mp hc
  rw [he] at hc'
  ring_nf at hc'
  apply (mul_lt_mul_iff_right₀ hq).mp
  field_simp
  nlinarith [hc']

private lemma zero_order_kernel {u p ν : ℝ} (hu : 0 < u) (hν : 0 < ν)
    (he : p^2 = 2*ν+1) :
    cosh u + ν*u*sinh u < cosh (p*u) := by
  have hc := (squared_order_strictConvex hu).lt_slope_of_hasDerivAt
    (show (1 : ℝ) ∈ Ici 0 by norm_num) (sq_nonneg p)
    (show 1 < p^2 by linarith) (cosh_sqrt_deriv u 1 (by norm_num))
  simp only [sqrt_one, mul_one, slope_def_field] at hc
  rw [cosh_sqrt_sq u p hu.le] at hc
  have hc' := (lt_div_iff₀ (show 0 < p^2-1 by linarith)).mp hc
  rw [he] at hc'
  ring_nf at hc' ⊢
  linarith

private lemma parameters {ν n : ℝ} (hn : n < 1)
    (hν : 1-n+sqrt (2*(1-n)) ≤ ν) :
    0 ≤ (ν+n)^2-2*ν-1 ∧
    sqrt ((ν+n)^2-2*ν-1) < ν ∧
    sqrt ((ν+n)^2-2*ν-1)+1 < ν+n := by
  have hd : 0 < 2*(1-n) := by linarith
  have hs := sqrt_pos_of_pos hd
  have hss := sq_sqrt hd.le
  have hv : sqrt (2*(1-n)) ≤ ν+n-1 := by linarith
  have hv0 : 0 < ν+n-1 := lt_of_lt_of_le hs hv
  have hdisc : 0 ≤ (ν+n)^2-2*ν-1 := by nlinarith
  have hq := sqrt_nonneg ((ν+n)^2-2*ν-1)
  have hq2 := sq_sqrt hdisc
  have hb : sqrt ((ν+n)^2-2*ν-1) < ν+n-1 := by nlinarith
  exact ⟨hdisc, by linarith, by linarith⟩


end D5.S3.Analytic.GauntBesselTail.Result
