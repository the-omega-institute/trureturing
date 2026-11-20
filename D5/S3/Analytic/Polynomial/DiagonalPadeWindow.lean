/- GID: D5/S3/Analytic/Polynomial/DiagonalPadeWindow
   generality: G
   mirror-B: D5/B/S3/Analytic/Polynomial/DiagonalPadeWindow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform strict positivity of odd diagonal Padé reciprocal coefficients. -/
module

public import D5.S3.Analytic.Polynomial.DiagonalPadeExterior
import all D5.S3.Analytic.Polynomial.DiagonalPadeExterior
import all D5.S3.Analytic.Polynomial.DiagonalPadeResidue
import all D5.S3.Analytic.HalfIntegerBessel
import all D5.S3.Analytic.Polynomial.DiagonalPadeExponential
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Strict positivity in the odd diagonal Padé window

Escape audit unfinished for the public theorems in this module.
https://github.com/the-omega-institute/trureturing/issues/32304
-/

public section

open Set Filter Asymptotics Metric Polynomial
open D5.S3.Analytic.HalfIntegerBessel (order eta)
open D5.S3.Analytic.Polynomial.DiagonalPadeExponential
open D5.S3.Analytic.Polynomial.DiagonalPadePhase
open D5.S3.Analytic.Polynomial.DiagonalPadeResidue
open D5.S3.Analytic.Polynomial.DiagonalPadeExterior
open scoped Topology

namespace D5.S3.Analytic.Polynomial.DiagonalPadeWindow

private theorem summable_shifted_gaussian {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable (fun j : ℤ => Real.exp (-a * ((j : ℝ) - x) ^ 2)) := by
  have hdecay := cexp_neg_quadratic_isLittleO_abs_rpow_cocompact
    (a := (↑(-a) : ℂ)) (by simpa) (↑(2 * a * x) : ℂ) (-2)
  have hdecay' := hdecay.isBigO.const_mul_left (Complex.exp (↑(-a * x ^ 2) : ℂ))
  have hsum := summable_of_isBigO (Real.summable_abs_int_rpow (b := 2) one_lt_two)
    (hdecay'.comp_tendsto Int.tendsto_coe_cofinite)
  apply hsum.norm.congr
  intro j
  rw [Function.comp_apply, ← Complex.exp_add, Complex.norm_exp]
  congr 1
  simp only [Complex.add_re, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

private theorem gaussian_poisson {α : ℝ} (hα : 0 < α) (θ : ℝ) :
    (∑' j : ℤ, Complex.exp ((↑(-α * (j : ℝ) ^ 2) : ℂ) +
        (↑((j : ℝ) * θ) : ℂ) * Complex.I)) =
      (↑((1 / Real.sqrt (α / Real.pi)) * ∑' j : ℤ,
        Real.exp (-(Real.pi / (α / Real.pi)) * ((j : ℝ) - θ / (2 * Real.pi)) ^ 2)) : ℂ) := by
  let a : ℝ := α / Real.pi
  let x : ℝ := θ / (2 * Real.pi)
  have ha : 0 < a := div_pos hα Real.pi_pos
  have hlinear : (2 * Real.pi * x : ℝ) = θ := by
    dsimp [x]
    field_simp
  have hquad : Real.pi * a = α := by dsimp [a]; field_simp
  have hI : Complex.I * ((x : ℂ) * Complex.I) = ↑(-x) := by
    rw [← mul_assoc, mul_comm Complex.I (x : ℂ), mul_assoc, Complex.I_mul_I]
    simp
  have hscale : (↑(1 / Real.sqrt a) : ℂ) = 1 / (a : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    push_cast [Complex.ofReal_cpow ha.le]
    norm_num
  have h := Complex.tsum_exp_neg_quadratic
    (a := (a : ℂ)) (by simpa using ha) ((x : ℂ) * Complex.I)
  calc
    _ = ∑' j : ℤ, Complex.exp (-↑Real.pi * (a : ℂ) * (j : ℂ) ^ 2 +
        2 * ↑Real.pi * ((x : ℂ) * Complex.I) * j) := by
      apply tsum_congr
      intro j
      congr 1
      rw [← hquad, ← hlinear]
      push_cast
      ring
    _ = _ := by
      change _ = (↑((1 / Real.sqrt a) * ∑' j : ℤ,
        Real.exp (-(Real.pi / a) * ((j : ℝ) - x) ^ 2)) : ℂ)
      rw [h, hI, Complex.ofReal_mul, hscale, Complex.ofReal_tsum]
      congr 1
      apply tsum_congr
      intro j
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring

/-- The real part of the Gaussian theta series has a uniform positive lower bound for
every real phase throughout the closed quadratic window. -/
theorem theta_real_lower_bound {c : ℝ} (hc : 0 < c) :
    let C := Real.pi ^ 2 * c ^ 2 / (2 * (1 + c ^ 2) ^ 2)
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ ∈ Icc (1 / 4 : ℝ) (1 / 2), ∀ θ : ℝ,
      δ ≤ (∑' j : ℤ, Complex.exp ((↑((-(C * τ) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
        (↑((j : ℝ) * θ) : ℂ) * Complex.I)).re := by
  dsimp only
  let C := Real.pi ^ 2 * c ^ 2 / (2 * (1 + c ^ 2) ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  let δ := (1 / Real.sqrt (C / (2 * Real.pi))) * Real.exp (-(Real.pi ^ 2 / C))
  refine ⟨δ, by dsimp [δ]; positivity, ?_⟩
  intro τ hτ θ
  change δ ≤ (∑' j : ℤ, Complex.exp ((↑((-(C * τ) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
    (↑((j : ℝ) * θ) : ℂ) * Complex.I)).re
  let α := C * τ
  let a := α / Real.pi
  let x := θ / (2 * Real.pi)
  have hα : 0 < α := mul_pos hC (lt_of_lt_of_le (by norm_num) hτ.1)
  have ha : 0 < a := div_pos hα Real.pi_pos
  rw [gaussian_poisson hα θ, Complex.ofReal_re]
  change δ ≤ (1 / Real.sqrt a) *
    ∑' j : ℤ, Real.exp (-(Real.pi / a) * ((j : ℝ) - x) ^ 2)
  let k := ⌊x + 1 / 2⌋
  have hk₁ := Int.floor_le (x + 1 / 2)
  have hk₂ := Int.lt_floor_add_one (x + 1 / 2)
  have hk : |(k : ℝ) - x| ≤ 1 / 2 := by
    rw [abs_le]
    change (k : ℝ) ≤ x + 1 / 2 at hk₁
    change x + 1 / 2 < (k : ℝ) + 1 at hk₂
    constructor <;> linarith
  have hsq : ((k : ℝ) - x) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs ((k : ℝ) - x)]
    calc
      _ ≤ (1 / 2 : ℝ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hk 2
      _ = _ := by norm_num
  have hα₁ : C / 4 ≤ α := by
    dsimp [α]
    linarith [mul_le_mul_of_nonneg_left hτ.1 hC.le]
  have hα₂ : α ≤ C / 2 := by
    dsimp [α]
    linarith [mul_le_mul_of_nonneg_left hτ.2 hC.le]
  have hratio : Real.pi / a / 4 ≤ Real.pi ^ 2 / C := by
    dsimp [a]
    apply (le_div_iff₀ hC).mpr
    have hh : 0 < 4 * α := by positivity
    rw [show Real.pi / (α / Real.pi) / 4 * C =
        (Real.pi ^ 2 * C) / (4 * α) by field_simp]
    have hCα : C ≤ 4 * α := by linarith
    exact (div_le_iff₀ hh).mpr (mul_le_mul_of_nonneg_left hCα (sq_nonneg Real.pi))
  have hscale : 1 / Real.sqrt (C / (2 * Real.pi)) ≤ 1 / Real.sqrt a := by
    apply one_div_le_one_div_of_le (Real.sqrt_pos.2 ha)
    apply Real.sqrt_le_sqrt
    dsimp [a]
    rw [show C / (2 * Real.pi) = (C / 2) / Real.pi by ring]
    exact div_le_div_of_nonneg_right hα₂ Real.pi_pos.le
  calc
    δ ≤ (1 / Real.sqrt a) * Real.exp (-(Real.pi / a) * ((k : ℝ) - x) ^ 2) := by
      apply mul_le_mul hscale _ (Real.exp_pos _).le (by positivity)
      apply Real.exp_le_exp.mpr
      have h := mul_le_mul_of_nonneg_left hsq (div_pos Real.pi_pos ha).le
      linarith
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_shifted_gaussian (div_pos Real.pi_pos ha) x).le_tsum k
        (fun j _ => (Real.exp_pos _).le)

private theorem order_pos (m : ℕ) : 0 < order m := by unfold order; positivity

private theorem natCast_le_order (m : ℕ) : (m : ℝ) ≤ order m := by unfold order; linarith

private theorem pole_term_norm_le {m n : ℕ} (hm : Odd m) {r W l : ℝ} {ζ : ℂ}
    (hr : 0 < r) (hW : residueWeight m (r : ℂ) = (W : ℂ))
    (hrroot : aeval (r : ℂ) (denominator m) = 0)
    (hroot : aeval ζ (denominator m) = 0)
    (hlNonneg : 0 ≤ l) (hgap : l ≤ Real.log (‖ζ‖ / r)) :
    ‖(residueWeight m ζ / (W : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
      Real.exp (-l * ((n : ℕ) : ℝ)) := by
  have hz := norm_pos_iff.mpr (denominator_root_derivative m hroot).1
  have hle : r ≤ ‖ζ‖ := by
    have hl := (Real.log_nonneg_iff (div_pos hz hr)).mp (hlNonneg.trans hgap)
    simpa only [one_mul] using (le_div_iff₀ hr).mp hl
  have hlog : Real.log (r / ‖ζ‖) ≤ -l := by
    rw [Real.log_div hr.ne' hz.ne']
    rw [Real.log_div hz.ne' hr.ne'] at hgap
    linarith
  rw [← hW]
  calc
    _ ≤ (r / ‖ζ‖) ^ (n + m + 1) :=
      norm_normalized_residueWeight_le m n hm hr hrroot hroot hle
    _ = Real.exp (((n + m + 1 : ℕ) : ℝ) * Real.log (r / ‖ζ‖)) := by
      rw [Real.exp_nat_mul, Real.exp_log (div_pos hr hz)]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hcast : (n : ℝ) ≤ ((n + m + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show n ≤ n + m + 1 by omega)
      calc
        _ ≤ ((n + m + 1 : ℕ) : ℝ) * (-l) := mul_le_mul_of_nonneg_left hlog (by positivity)
        _ ≤ _ := by
          simpa only [mul_comm] using mul_le_mul_of_nonpos_right hcast (neg_nonpos.mpr hlNonneg)

private theorem central_term_norm_le {m n : ℕ} (hm : Odd m) {r W C : ℝ}
    {ζ : ℂ} {j : ℤ} (hr : 0 < r) (hW : residueWeight m (r : ℂ) = (W : ℂ))
    (hrroot : aeval (r : ℂ) (denominator m) = 0)
    (hroot : aeval ζ (denominator m) = 0) (hC : 0 < C)
    (hn : 1 / 4 ≤ (n : ℝ) / order m ^ 2)
    (hgap : C / 2 * ((j : ℝ) / order m) ^ 2 ≤ Real.log (‖ζ‖ / r)) :
    ‖(residueWeight m ζ / (W : ℂ)) * ((r : ℂ) / ζ) ^ n‖ ≤
      Real.exp (-(C / 8) * (j : ℝ) ^ 2) := by
  refine (pole_term_norm_le hm hr hW hrroot hroot (by positivity) hgap).trans ?_
  apply Real.exp_le_exp.mpr
  have hν := order_pos m
  rw [div_pow]
  have h := mul_le_mul_of_nonneg_left hn (show 0 ≤ C / 2 * (j : ℝ) ^ 2 by positivity)
  calc
    _ = -(C / 2 * (j : ℝ) ^ 2 * ((n : ℝ) / order m ^ 2)) := by ring
    _ ≤ _ := by linarith

private theorem gaussian_term_norm_le {C τ θ : ℝ} (hC : 0 < C) (hτ : 1 / 4 ≤ τ)
    (j : ℤ) :
    ‖Complex.exp ((↑((-(C * τ) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
      (↑((j : ℝ) * θ) : ℂ) * Complex.I)‖ ≤ Real.exp (-(C / 8) * (j : ℝ) ^ 2) := by
  rw [Complex.norm_exp, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero,
    Real.exp_le_exp]
  have h := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hτ hC.le) (sq_nonneg (j : ℝ))
  have h' : 0 ≤ C * (j : ℝ) ^ 2 := by positivity
  linarith

private theorem exists_gaussian_tail_finset {C ε : ℝ} (hC : 0 < C) (hε : 0 < ε) :
    ∃ S : Finset ℤ, (∑' j : ↥((S : Set ℤ)ᶜ), Real.exp (-(C / 8) * (j : ℝ) ^ 2)) < ε := by
  let f (j : ℤ) := Real.exp (-(C / 8) * (j : ℝ) ^ 2)
  have hs : Summable f := by simpa [f] using summable_shifted_gaussian (by positivity : 0 < C / 8) 0
  have ht := hs.hasSum
  rw [HasSum, Metric.tendsto_nhds] at ht
  obtain ⟨S, hS⟩ := (ht ε hε).exists
  refine ⟨S, ?_⟩
  have he := hs.sum_add_tsum_compl (s := S)
  have hh : dist (∑ j ∈ S, f j) (∑' j, f j) < ε := hS
  rw [dist_eq_norm, norm_sub_rev, ← he, add_sub_cancel_left] at hh
  exact (Real.le_norm_self _).trans_lt hh

private theorem norm_sum_sub_tsum_le_gaussian_tail {C τ θ : ℝ} (hC : 0 < C) (hτ : 1 / 4 ≤ τ)
    (S : Finset ℤ) :
    let f := fun j : ℤ => Complex.exp ((↑((-(C * τ) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
      (↑((j : ℝ) * θ) : ℂ) * Complex.I)
    ‖(∑ j ∈ S, f j) - ∑' j, f j‖ ≤
      ∑' j : ↥((S : Set ℤ)ᶜ), Real.exp (-(C / 8) * (j : ℝ) ^ 2) := by
  dsimp only
  let f := fun j : ℤ => Complex.exp ((↑((-(C * τ) * (j : ℝ) ^ 2) : ℝ) : ℂ) +
    (↑((j : ℝ) * θ) : ℂ) * Complex.I)
  change ‖(∑ j ∈ S, f j) - ∑' j, f j‖ ≤ _
  have hs : Summable (fun j : ℤ => Real.exp (-(C / 8) * (j : ℝ) ^ 2)) := by
    simpa using summable_shifted_gaussian (by positivity : 0 < C / 8) 0
  have hf : Summable (fun j => ‖f j‖) := hs.of_nonneg_of_le (fun _ => norm_nonneg _)
    (gaussian_term_norm_le (θ := θ) hC hτ)
  rw [← hf.of_norm.sum_add_tsum_compl (s := S), sub_add_cancel_left, norm_neg]
  exact (norm_tsum_le_tsum_norm (hf.subtype _)).trans
    ((hf.subtype _).tsum_le_tsum (fun j => gaussian_term_norm_le (θ := θ) hC hτ j) (hs.subtype _))

private theorem finite_tail_le_gaussian_tail {C : ℝ} (hC : 0 < C) {S T : Finset ℤ}
    (hT : Disjoint T S) :
    (∑ j ∈ T, Real.exp (-(C / 8) * (j : ℝ) ^ 2)) ≤
      ∑' j : ↥((S : Set ℤ)ᶜ), Real.exp (-(C / 8) * (j : ℝ) ^ 2) := by
  classical
  let f := fun j : ℤ => Real.exp (-(C / 8) * (j : ℝ) ^ 2)
  have hs : Summable f := by simpa [f] using summable_shifted_gaussian (by positivity : 0 < C / 8) 0
  change (∑ j ∈ T, f j) ≤ ∑' j : ↥((S : Set ℤ)ᶜ), f j
  have h := hs.sum_le_tsum (S ∪ T) (fun j _ => (Real.exp_pos _).le)
  rw [Finset.sum_union hT.symm, ← hs.sum_add_tsum_compl (s := S)] at h
  exact le_of_add_le_add_left h

private theorem exterior_exp_le_inv_order {Λ : ℝ} (hΛ : 0 < Λ) (m : ℕ) :
    (m : ℝ) * Real.exp (-Λ * order m ^ 2 / 4) ≤ (4 / Λ) / order m := by
  let x := Λ * order m ^ 2 / 4
  have hν := order_pos m
  have hx : 0 < x := by dsimp [x]; positivity
  have he : x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  have hi : 1 / Real.exp x ≤ 1 / x :=
    one_div_le_one_div_of_le hx he
  calc
    _ = (m : ℝ) * (1 / Real.exp x) := by
      rw [one_div, ← Real.exp_neg, show -Λ * order m ^ 2 / 4 = -x by ring]
    _ ≤ order m * (1 / x) := mul_le_mul (natCast_le_order m) hi (by positivity) hν.le
    _ = _ := by dsimp [x]; field_simp

private theorem exists_full_central_indices (m : ℕ) (t₀ : ℝ) :
    ∃ T : Finset ℤ, ∀ j : ℤ, j ∈ T ↔ ‖polePhaseLattice m j‖ ≤ t₀ := by
  classical
  obtain ⟨L, hL⟩ := exists_nat_gt (t₀ * order m / Real.pi)
  refine ⟨(Finset.Icc (-(L : ℤ)) (L : ℤ)).filter (fun j => ‖polePhaseLattice m j‖ ≤ t₀), ?_⟩
  intro j
  rw [Finset.mem_filter, Finset.mem_Icc, and_iff_right_iff_imp]
  intro hj
  rw [norm_polePhaseLattice] at hj
  have habs : |(j : ℝ)| ≤ (L : ℝ) := by
    apply le_of_lt
    apply lt_of_le_of_lt _ hL
    apply (le_div_iff₀ Real.pi_pos).mpr
    have h := (div_le_iff₀ (order_pos m)).mp hj
    simpa only [mul_comm] using h
  rw [abs_le] at habs
  exact ⟨by exact_mod_cast habs.1, by exact_mod_cast habs.2⟩

/-- One threshold gives strict positivity of the native rational reciprocal coefficients
for every odd diagonal order throughout the closed quadratic window. -/
theorem exists_uniform_reciprocalCoefficient_pos :
    ∃ M : ℕ, ∀ m ≥ M, Odd m → ∀ n : ℕ,
      (n : ℝ) / order m ^ 2 ∈ Icc (1 / 4) (1 / 2) →
      0 < reciprocalCoefficient m n := by
  classical
  obtain ⟨c, hc, hc1, hcη, _, _⟩ := exists_eta_positive_zero
  let C := Real.pi ^ 2 * c ^ 2 / (2 * (1 + c ^ 2) ^ 2)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨δ, hδ, hθ⟩ := theta_real_lower_bound hc
  obtain ⟨S, hS⟩ := exists_gaussian_tail_finset (C := C) (ε := δ / 8) hC (by positivity)
  obtain ⟨t₀, ε, _, B, K, ht₀, hε, _, _, _, hcutoff, M₁, hcentral⟩ :=
    exists_central_residue_comparison_with_bounds hc hcη
  obtain ⟨d, hd, M₂, hexterior⟩ := exists_uniform_scaled_exterior_radius hc hc1 hcη hε
  let J := S.sup Int.natAbs
  obtain ⟨M₃, hJ⟩ := hcutoff J
  let Λ := Real.log ((c + d) / (c + d / 2))
  have hΛ : 0 < Λ := Real.log_pos ((one_lt_div₀ (by positivity)).mpr (by linarith))
  let P := ∑ j ∈ S, B * (|(j : ℝ)| + (j : ℝ) ^ 2 + |(j : ℝ)| ^ 3)
  obtain ⟨N, hN⟩ := exists_nat_gt (max 1 (max (K / (d / 2))
    (max (P / (δ / 8)) ((4 / Λ) / (δ / 8)))))
  refine ⟨max (max M₁ M₂) (max M₃ N), ?_⟩
  intro m hm hodd n hn
  have hm₁ : M₁ ≤ m := by omega
  have hm₂ : M₂ ≤ m := by omega
  have hm₃ : M₃ ≤ m := by omega
  have hmN : N ≤ m := by omega
  have hν := order_pos m
  have hNν : (N : ℝ) ≤ order m :=
    (show (N : ℝ) ≤ (m : ℝ) by exact_mod_cast hmN).trans (natCast_le_order m)
  have hν₁ : 1 ≤ order m := (le_max_left _ _).trans (hN.le.trans hNν)
  have hνsq : order m ≤ order m ^ 2 := by nlinarith
  have hclose : K / order m ^ 2 ≤ d / 2 := by
    have h := (le_max_left (K / (d / 2)) _).trans
      ((le_max_right (1 : ℝ) _).trans (hN.le.trans (hNν.trans hνsq)))
    exact (div_le_iff₀ (sq_pos_of_pos hν)).mpr
      (mul_comm (d / 2) _ ▸ (div_le_iff₀ (by positivity : 0 < d / 2)).mp h)
  have hP : P / order m ≤ δ / 8 := by
    have h := (le_max_left (P / (δ / 8)) _).trans
      ((le_max_right (K / (d / 2)) _).trans ((le_max_right (1 : ℝ) _).trans (hN.le.trans hNν)))
    exact (div_le_iff₀ hν).mpr
      (mul_comm (δ / 8) _ ▸ (div_le_iff₀ (by positivity : 0 < δ / 8)).mp h)
  have hexp : (4 / Λ) / order m ≤ δ / 8 := by
    have h := (le_max_right (P / (δ / 8)) _).trans
      ((le_max_right (K / (d / 2)) _).trans ((le_max_right (1 : ℝ) _).trans (hN.le.trans hNν)))
    exact (div_le_iff₀ hν).mpr
      (mul_comm (δ / 8) _ ▸ (div_le_iff₀ (by positivity : 0 < δ / 8)).mp h)
  obtain ⟨g, r, W, hr, hW, hr₀, hweight, hgclose, hquad, hinj, hlocal, _, _, hpoint⟩ :=
    hcentral m hm₁ hodd
  have hroot (j : ℤ) (hj : ‖polePhaseLattice m j‖ ≤ t₀) :
      aeval (centralPole m g j) (denominator m) = 0 := (hpoint j hj).1
  have hrroot : aeval (r : ℂ) (denominator m) = 0 := by
    rw [← hr₀]
    exact hroot 0 (by simp [polePhaseLattice, ht₀.le])
  have hrdef : r = 2 * order m * (g 0).re := by
    have h := congrArg Complex.re hr₀
    simpa [centralPole, polePhaseLattice, Complex.mul_re, Complex.mul_im] using h.symm
  have hgre : 0 < (g 0).re := by
    have h := hr
    rw [hrdef] at h
    exact pos_of_mul_pos_right h (by positivity)
  have hgap := exterior_log_gap hc hd hgre hrdef (hgclose.trans hclose)
    hlocal (hexterior m hm₂ hodd)
  let f (ζ : ℂ) : ℂ := (residueWeight m ζ / (W : ℂ)) * ((r : ℂ) / ζ) ^ n
  have houtside : ‖∑ ζ ∈ exteriorPoles m g t₀, f ζ‖ ≤ δ / 8 := by
    have h := norm_sum_normalized_exterior_le m n hodd hΛ hr hrroot
      (g := g) (t₀ := t₀) (fun ζ hz => by
        have hz' := Finset.mem_filter.mp hz
        exact hgap ζ (mem_aroots.mp (Multiset.mem_toFinset.mp hz'.1)).2 hz'.2) hn.1
    rw [hweight] at h
    exact h.trans ((exterior_exp_le_inv_order hΛ m).trans hexp)
  obtain ⟨T, hT⟩ := exists_full_central_indices m t₀
  have hST : S ⊆ T := by
    intro j hj
    apply (hT j).mpr
    apply hJ m hm₃ j
    have h := Finset.le_sup (f := Int.natAbs) hj
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
    exact_mod_cast h
  have hTinj : Set.InjOn (centralPole m g) (↑T : Set ℤ) :=
    hinj.mono fun j hj => (hT j).mp hj
  let roots := ((denominator m).aroots ℂ).toFinset
  have hcentralRoots : ∀ j ∈ T, centralPole m g j ∈ roots := by
    intro j hj
    exact Multiset.mem_toFinset.mpr ((mem_aroots).mpr
      ⟨denominator_ne_zero m, hroot j ((hT j).mp hj)⟩)
  have hrootSplit : roots = T.image (centralPole m g) ∪ exteriorPoles m g t₀ := by
    ext ζ
    rw [Finset.mem_union, exteriorPoles, Finset.mem_filter]
    change ζ ∈ roots ↔ ζ ∈ T.image (centralPole m g) ∨ ζ ∈ roots ∧ _
    constructor
    · intro hζ
      by_cases hmem : ζ ∈ T.image (centralPole m g)
      · exact Or.inl hmem
      · exact Or.inr ⟨hζ, fun j hj he => hmem (Finset.mem_image.mpr ⟨j, (hT j).mpr hj, he.symm⟩)⟩
    · rintro (hζ | hζ)
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hζ
        exact hcentralRoots j hj
      · exact hζ.1
  have hdisj : Disjoint (T.image (centralPole m g)) (exteriorPoles m g t₀) := by
    refine Finset.disjoint_left.mpr ?_
    intro ζ hz he
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact (Finset.mem_filter.mp he).2 j ((hT j).mp hj) rfl
  have hsplit : ∑ ζ ∈ roots, f ζ =
      (∑ j ∈ S, f (centralPole m g j)) +
      (∑ j ∈ T \ S, f (centralPole m g j)) +
      (∑ ζ ∈ exteriorPoles m g t₀, f ζ) := by
    rw [hrootSplit, Finset.sum_union hdisj, Finset.sum_image hTinj]
    rw [add_comm (∑ j ∈ S, f (centralPole m g j)), Finset.sum_sdiff hST]
  let τ := (n : ℝ) / order m ^ 2
  let b := 1 / Real.sqrt (1 + c ^ 2)
  let θ := Real.pi * (c / Real.sqrt (1 + c ^ 2) - b - 1) -
      Real.pi * b * (n : ℝ) / order m
  let F (j : ℤ) : ℂ := Complex.exp ((↑(-(C * τ) * (j : ℝ) ^ 2) : ℂ) +
    ↑((j : ℝ) * θ) * Complex.I)
  have hF (j : ℤ) : F j = Complex.exp (gaussianSummandExponent c m n j) := by
    have hcoef : C = Real.pi ^ 2 * (c ^ 2 / (2 * (1 + c ^ 2) ^ 2)) := by
      dsimp [C]
      ring
    simp only [F, gaussianSummandExponent, hcoef, τ, θ, b, neg_mul]
  have hfinite : ‖(∑ j ∈ S, f (centralPole m g j)) - ∑ j ∈ S, F j‖ ≤ δ / 8 := by
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (le_trans ?_ hP)
    rw [show P / order m = _ from Finset.sum_div ..]
    apply Finset.sum_le_sum
    intro j hj
    rw [hF]
    exact ((hpoint j ((hT j).mp (hST hj))).2.2 n hn).2.2
  have hcentralTail : ‖∑ j ∈ T \ S, f (centralPole m g j)‖ ≤ δ / 8 := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum ?_).trans
      ((finite_tail_le_gaussian_tail hC Finset.sdiff_disjoint).trans hS.le))
    intro j hj
    have hj' := (hT j).mp (Finset.mem_sdiff.mp hj).1
    refine central_term_norm_le hodd hr hweight hrroot (hroot j hj') hC hn.1 ?_
    convert hquad j hj' using 1
    dsimp [C]
    field_simp
    <;> ring
  have hthetaTail : ‖(∑ j ∈ S, F j) - ∑' j, F j‖ ≤ δ / 8 :=
    (norm_sum_sub_tsum_le_gaussian_tail (θ := θ) hC hn.1 S).trans hS.le
  have herror : ‖(∑ ζ ∈ roots, f ζ) - ∑' j, F j‖ ≤ δ / 2 := by
    rw [hsplit, show (∑ j ∈ S, f (centralPole m g j)) + (∑ j ∈ T \ S, f (centralPole m g j)) +
        (∑ ζ ∈ exteriorPoles m g t₀, f ζ) - (∑' j, F j) =
        ((∑ j ∈ S, f (centralPole m g j)) - ∑ j ∈ S, F j) +
        ((∑ j ∈ S, F j) - ∑' j, F j) +
        (∑ j ∈ T \ S, f (centralPole m g j)) +
        (∑ ζ ∈ exteriorPoles m g t₀, f ζ) by abel]
    have h := norm_add_le_of_le (norm_add_le_of_le (norm_add_le_of_le hfinite hthetaTail)
      hcentralTail) houtside
    exact h.trans (by ring_nf; exact le_rfl)
  have hpositive : 0 < (∑ ζ ∈ roots, f ζ).re := by
    have hlo := hθ τ hn θ
    change δ ≤ (∑' j, F j).re at hlo
    have hz := (abs_le.mp ((Complex.abs_re_le_norm ((∑ ζ ∈ roots, f ζ) -
      ∑' j, F j)).trans herror)).1
    have hdiff := hz
    rw [Complex.sub_re] at hdiff
    linarith
  have hnormalized : (∑ ζ ∈ roots, f ζ) =
      (↑((reciprocalCoefficient m n : ℚ) : ℝ) : ℂ) * (r : ℂ) ^ n / (W : ℂ) := by
    rw [Complex.ofReal_ratCast, reciprocalCoefficient_eq_sum m n hodd.pos, Finset.sum_mul,
      Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ζ _
    dsimp [f]
    rw [div_eq_mul_inv (r : ℂ), mul_pow]
    ring
  rw [hnormalized, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_div,
    Complex.ofReal_re] at hpositive
  have hp := (div_pos_iff_of_pos_right hW).mp hpositive
  exact_mod_cast (pos_of_mul_pos_left hp (by positivity : 0 ≤ r ^ n))

end D5.S3.Analytic.Polynomial.DiagonalPadeWindow
