/- GID: D5/S3/Arith/Robin/ZeroCoefficientBudget
   generality: G
   mirror-B: D5/B/S3/Arith/Robin/ZeroCoefficientBudget
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: A conjugate zero family has an absolute coefficient and height budget. -/

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Trigonometric

/-! A mass identity for a conjugate family controls its absolute zero response. -/

namespace D5.S3.Arith.Robin.ZeroCoefficientBudget

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

/-- The coefficient of one zero occurrence. -/
def coefficient {ι : Type*} (ρ : ι → ℂ) (i : ι) : ℂ := (ρ i * (1 - ρ i))⁻¹

/-- The prescribed total mass. -/
def massConstant : ℝ := 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi)

/-- The absolutely convergent zero exponential series. -/
def Hc {ι : Type*} (ρ : ι → ℂ) (y : ℝ) : ℂ :=
  ∑' i, coefficient ρ i * Complex.exp (ρ i * (y : ℂ))

/-- The real zero response. -/
def H {ι : Type*} (ρ : ι → ℂ) (y : ℝ) : ℝ := (Hc ρ y).re

private theorem coefficient_bounds (z : ℂ) (hb : 0 < z.re ∧ z.re < 1)
    (hη : 10 < |z.im|) :
    (z.im ^ 2)⁻¹ ≤ 2 * (z * (1 - z))⁻¹.re ∧
      ‖(z * (1 - z))⁻¹‖ ≤ (z.im ^ 2)⁻¹ := by
  let p : ℝ := z.re * (1 - z.re)
  let q : ℝ := Complex.normSq (z * (1 - z))
  have hp : 0 < p := mul_pos hb.1 (sub_pos.mpr hb.2)
  have hp1 : p ≤ 1 / 4 := by dsimp [p]; nlinarith [sq_nonneg (z.re - 1 / 2)]
  have hη2 : 100 < z.im ^ 2 := by nlinarith [sq_abs z.im]
  have hη0 : 0 < z.im ^ 2 := by linarith
  have hreal : (z * (1 - z)).re = z.im ^ 2 + p := by
    simp [Complex.mul_re, p]; ring
  have hq : q = z.im ^ 4 + z.im ^ 2 * (1 - 2 * p) + p ^ 2 := by
    dsimp [q, p]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.one_re, Complex.sub_im, Complex.one_im]
    ring
  have hqlo : z.im ^ 4 ≤ q := by
    rw [hq]
    nlinarith [mul_nonneg (sq_nonneg z.im) (show 0 ≤ 1 - 2 * p by linarith), sq_nonneg p]
  have hqhi : q ≤ 2 * z.im ^ 4 := by
    rw [hq]
    have hp2 : p ^ 2 ≤ p := by nlinarith
    nlinarith [mul_nonneg (show 0 ≤ z.im ^ 2 - 1 by linarith) hp.le,
      sq_nonneg (z.im ^ 2 - 1)]
  have hη4 : 0 < z.im ^ 4 := by nlinarith [sq_pos_of_pos hη0]
  have hqpos : 0 < q := hη4.trans_le hqlo
  constructor
  · rw [Complex.inv_re, hreal]
    change (z.im ^ 2)⁻¹ ≤ 2 * ((z.im ^ 2 + p) / q)
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hqpos).2
    have hcancel : (z.im ^ 2)⁻¹ * z.im ^ 4 = z.im ^ 2 := by
      field_simp
    have h := mul_le_mul_of_nonneg_left hqhi (inv_nonneg.mpr hη0.le)
    nlinarith
  · rw [norm_inv]
    apply inv_anti₀ hη0
    apply (sq_le_sq₀ (sq_nonneg _) (norm_nonneg _)).mp
    simpa only [Complex.sq_norm, ← pow_mul] using hqlo

private theorem massConstant_lt_one : massConstant < 1 := by
  have he : Real.exp 2 < 4 * Real.pi := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1, Real.pi_gt_three]
  have hlog : 2 < Real.log (4 * Real.pi) :=
    (Real.lt_log_iff_exp_lt (by positivity)).2 he
  dsimp [massConstant]
  linarith [Real.eulerMascheroniConstant_lt_two_thirds]

/-- The mass identity controls absolute convergence, height multiplicities, and the real response. -/
theorem zero_coefficient_budget {ι : Type*} [Countable ι] (ρ : ι → ℂ)
    (hstrip : ∀ i, 0 < (ρ i).re ∧ (ρ i).re < 1)
    (conjIndex : ι ≃ ι) (hconj : ∀ i, ρ (conjIndex i) = star (ρ i))
    (hlow : ∀ i, 10 < |(ρ i).im|)
    (hmass : HasSum (fun i => (ρ i * (1 - ρ i))⁻¹) (massConstant : ℂ)) :
    Summable (fun i => ‖coefficient ρ i‖) ∧
    Summable (fun i => ((ρ i).im ^ 2)⁻¹) ∧
    (∑' i, ((ρ i).im ^ 2)⁻¹) ≤ 2 * massConstant ∧
    2 * massConstant < 2 ∧
    (∑' i, ‖coefficient ρ i‖) < 2 ∧
    (∀ T : ℝ, 0 < T → Set.Finite {i | |(ρ i).im| ≤ T} ∧
      (({i | |(ρ i).im| ≤ T} : Set ι).ncard : ℝ) ≤ 2 * T ^ 2) ∧
    (∀ y : ℝ, Summable (fun i => coefficient ρ i * Complex.exp (ρ i * (y : ℂ))) ∧
      Hc ρ y = (H ρ y : ℂ) ∧ |H ρ y| ≤ 2 * Real.exp (max y 0)) ∧
    (∀ i, ((ρ i).im ^ 2)⁻¹ ≤ 2 * (coefficient ρ i).re ∧
      ‖coefficient ρ i‖ ≤ ((ρ i).im ^ 2)⁻¹) := by
  classical
  have ha : Summable (coefficient ρ) := hmass.summable
  have han : Summable (fun i => ‖coefficient ρ i‖) := ha.norm
  have hre : HasSum (fun i => (coefficient ρ i).re) massConstant := by
    simpa [coefficient] using Complex.hasSum_re hmass
  have hbounds := fun i => coefficient_bounds (ρ i) (hstrip i) (hlow i)
  have hinv : Summable (fun i => ((ρ i).im ^ 2)⁻¹) :=
    Summable.of_nonneg_of_le (fun i => inv_nonneg.mpr (sq_nonneg _))
      (fun i => (hbounds i).1) (hre.summable.mul_left 2)
  have hsum : (∑' i, ((ρ i).im ^ 2)⁻¹) ≤ 2 * massConstant := by
    calc
      _ ≤ ∑' i, 2 * (coefficient ρ i).re := hinv.tsum_le_tsum (fun i => (hbounds i).1)
        (hre.summable.mul_left 2)
      _ = 2 * massConstant := by rw [tsum_mul_left, hre.tsum_eq]
  have hc : 2 * massConstant < 2 := by linarith [massConstant_lt_one]
  have hnorm : (∑' i, ‖coefficient ρ i‖) < 2 :=
    (han.tsum_le_tsum (fun i => (hbounds i).2) hinv).trans_lt (hsum.trans_lt hc)
  refine ⟨han, hinv, hsum, hc, hnorm, ?_, ?_, hbounds⟩
  · intro T hT
    let s : Set ι := {i | |(ρ i).im| ≤ T}
    have hT2 : 0 < T ^ 2 := sq_pos_of_pos hT
    have hpoint (i : s) : (T ^ 2)⁻¹ ≤ ((ρ i).im ^ 2)⁻¹ := by
      apply inv_anti₀ (by nlinarith [hlow i.1, sq_abs (ρ i.1).im])
      have hi : |(ρ i.1).im| ≤ T := i.2
      nlinarith [abs_nonneg (ρ i.1).im, sq_abs (ρ i.1).im]
    have hconst : Summable (fun _ : s => (T ^ 2)⁻¹) :=
      Summable.of_nonneg_of_le (fun _ => by positivity) hpoint (hinv.subtype s)
    let : Finite s := Finite.of_summable_const (by positivity) hconst
    have hs : s.Finite := Set.toFinite s
    refine ⟨hs, ?_⟩
    have hcount : (s.ncard : ℝ) * (T ^ 2)⁻¹ ≤ ∑' i, ((ρ i).im ^ 2)⁻¹ := by
      calc
        _ = ∑ i ∈ hs.toFinset, (T ^ 2)⁻¹ := by
          rw [Set.ncard_eq_toFinset_card s hs]; simp
        _ ≤ ∑ i ∈ hs.toFinset, ((ρ i).im ^ 2)⁻¹ :=
          Finset.sum_le_sum fun i hi => hpoint ⟨i, hs.mem_toFinset.mp hi⟩
        _ ≤ _ := hinv.sum_le_tsum _ (fun _ _ => by positivity)
    have hcount2 := mul_le_mul_of_nonneg_right (hcount.trans (hsum.trans hc.le)) hT2.le
    simpa only [mul_assoc, inv_mul_cancel₀ hT2.ne', mul_one] using hcount2
  · intro y
    have hterm (i : ι) : ‖coefficient ρ i * Complex.exp (ρ i * (y : ℂ))‖ ≤
        ‖coefficient ρ i‖ * Real.exp (max y 0) := by
      rw [norm_mul, Complex.norm_exp]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rcases le_total 0 y with hy | hy
      · rw [max_eq_left hy]; nlinarith [(hstrip i).2]
      · rw [max_eq_right hy]; nlinarith [(hstrip i).1]
    have hy : Summable (fun i => coefficient ρ i * Complex.exp (ρ i * (y : ℂ))) :=
      (han.mul_right (Real.exp (max y 0))).of_norm_bounded hterm
    have hstar : star (Hc ρ y) = Hc ρ y := by
      rw [Hc, tsum_star]
      calc
        (∑' i, star (coefficient ρ i * Complex.exp (ρ i * (y : ℂ)))) =
            ∑' i, coefficient ρ (conjIndex i) * Complex.exp (ρ (conjIndex i) * (y : ℂ)) := by
          apply tsum_congr
          intro i
          simp only [coefficient, hconj, Complex.star_def, map_mul, map_inv₀, map_sub, map_one,
            ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
        _ = _ := conjIndex.tsum_eq (fun i => coefficient ρ i * Complex.exp (ρ i * (y : ℂ)))
    have hreal : Hc ρ y = (H ρ y : ℂ) := by
      exact (Complex.conj_eq_iff_re.mp (by simpa only [Complex.star_def] using hstar)).symm
    refine ⟨hy, hreal, ?_⟩
    have hn : ‖Hc ρ y‖ ≤ (∑' i, ‖coefficient ρ i‖) * Real.exp (max y 0) := by
      calc
        _ ≤ ∑' i, ‖coefficient ρ i‖ * Real.exp (max y 0) :=
          tsum_of_norm_bounded (han.mul_right _).hasSum hterm
        _ = _ := tsum_mul_right
    rw [hreal, Complex.norm_real, Real.norm_eq_abs] at hn
    exact hn.trans (mul_le_mul_of_nonneg_right hnorm.le (Real.exp_pos _).le)

end

end D5.S3.Arith.Robin.ZeroCoefficientBudget
