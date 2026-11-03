/- GID: D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/FiniteGaussianMellin
   generality: G
   mirror-B: none(waiver:formal-unit-only)
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Central Mellin integrability and exact mass for finite real Gaussian sources. -/
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! Central Mellin integrability and exact mass for finite real Gaussian sources. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FiniteGaussianCap4
open MeasureTheory Set Filter
open scoped BigOperators

/-- The physical atom f_a(x)=exp(9a/2-exp(2a)*x), with no tail cutoff. -/
def gaussianAtom (a x : ℝ) : ℝ :=
  Real.exp ((9 / 2 : ℝ) * a - Real.exp (2 * a) * x)

/-- Arbitrary finite real Gaussian source, with repeated sites permitted. -/
def gaussianFeature {ι : Type*} [Fintype ι] (c site : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * gaussianAtom (site i) x

private theorem atom_split (a x : ℝ) :
    gaussianAtom a x = Real.exp ((9 / 2 : ℝ) * a) *
      Real.exp (-(Real.exp (2 * a) * x)) := by
  unfold gaussianAtom
  rw [sub_eq_add_neg, Real.exp_add]

private theorem mellin_atom (a : ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * gaussianAtom a x) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, x ^ (5 / 4 : ℝ) * gaussianAtom a x) =
        Real.Gamma (9 / 4 : ℝ) := by
  let r : ℝ := Real.exp (2 * a)
  have hr : 0 < r := Real.exp_pos _
  have hbase : IntegrableOn
      (fun y : ℝ => y ^ (5 / 4 : ℝ) * Real.exp (-y)) (Ioi 0) := by
    simpa only [show (9 / 4 : ℝ) - 1 = 5 / 4 by norm_num, mul_comm] using
      (Real.GammaIntegral_convergent (s := (9 / 4 : ℝ)) (by norm_num))
  have hscaled : IntegrableOn
      (fun x : ℝ => (r * x) ^ (5 / 4 : ℝ) * Real.exp (-(r * x))) (Ioi 0) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun y : ℝ => y ^ (5 / 4 : ℝ) * Real.exp (-y)) 0 hr).2
    simpa only [mul_zero] using hbase
  have hrpow : r ^ (5 / 4 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have hi : IntegrableOn
      (fun x : ℝ => x ^ (5 / 4 : ℝ) * Real.exp (-(r * x))) (Ioi 0) := by
    apply (hscaled.const_mul ((r ^ (5 / 4 : ℝ))⁻¹)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.mul_rpow hr.le (show 0 ≤ x from hx.le)]
    field_simp [hrpow]
    <;> ring
  have hfun : (fun x : ℝ => x ^ (5 / 4 : ℝ) * gaussianAtom a x) =
      (fun x : ℝ => Real.exp ((9 / 2 : ℝ) * a) *
        (x ^ (5 / 4 : ℝ) * Real.exp (-(r * x)))) := by
    funext x
    rw [atom_split]
    dsimp only [r]
    ring
  have hcancel : Real.exp ((9 / 2 : ℝ) * a) *
      (1 / r) ^ (9 / 4 : ℝ) = 1 := by
    dsimp only [r]
    rw [one_div, ← Real.exp_neg, ← Real.exp_mul, ← Real.exp_add]
    rw [show (9 / 2 : ℝ) * a + (-(2 * a)) * (9 / 4 : ℝ) = 0 by ring,
      Real.exp_zero]
  have hint := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (9 / 4 : ℝ)) (r := r) (by norm_num) hr
  norm_num only [show (9 / 4 : ℝ) - 1 = 5 / 4 by norm_num] at hint
  rw [hfun]
  refine ⟨hi.const_mul _, ?_⟩
  rw [integral_const_mul, hint, ← mul_assoc, hcancel, one_mul]

/-- Central Mellin supplier on the actual finite source, including absolute
integrability. A mass-zero coefficient family makes the right side zero.
There is no assumed expansion, basis, integral-domain witness, or target bound. -/
theorem finite_gaussian_mellin {ι : Type*} [Fintype ι] (c site : ι → ℝ) :
    IntegrableOn (fun x : ℝ => x ^ (5 / 4 : ℝ) * gaussianFeature c site x) (Ioi 0) ∧
      (∫ x : ℝ in Ioi 0, x ^ (5 / 4 : ℝ) * gaussianFeature c site x) =
        Real.Gamma (9 / 4 : ℝ) * ∑ i, c i := by
  have hterm (i : ι) : IntegrableOn
      (fun x : ℝ => c i * (x ^ (5 / 4 : ℝ) * gaussianAtom (site i) x)) (Ioi 0) :=
    (mellin_atom (site i)).1.const_mul (c i)
  have hfun : (fun x : ℝ => x ^ (5 / 4 : ℝ) * gaussianFeature c site x) =
      (fun x : ℝ => ∑ i, c i * (x ^ (5 / 4 : ℝ) * gaussianAtom (site i) x)) := by
    funext x
    simp only [gaussianFeature, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  refine ⟨integrable_finsetSum Finset.univ (fun i _ => hterm i), ?_⟩
  rw [integral_finsetSum Finset.univ (fun i _ => hterm i)]
  simp_rw [integral_const_mul]
  have hvalue (i : ι) :
      (∫ x : ℝ in Ioi 0, x ^ (5 / 4 : ℝ) * gaussianAtom (site i) x) =
        Real.Gamma (9 / 4 : ℝ) := (mellin_atom (site i)).2
  simp_rw [hvalue]
  rw [← Finset.sum_mul]
  ring

end FiniteGaussianCap4
