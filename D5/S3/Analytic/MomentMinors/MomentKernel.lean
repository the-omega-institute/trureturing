/- GID: D5/S3/Analytic/MomentMinors/MomentKernel
   generality: G
   mirror-B: D5/B/S3/Analytic/MomentMinors/MomentKernel
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Convex.Deriv, mathlib/module/Mathlib.Analysis.SpecialFunctions.Pow.Deriv, mathlib/module/Mathlib.LinearAlgebra.Matrix.PosDef, mathlib/module/Mathlib.InformationTheory.KullbackLeibler.KLFun]
   utility: none
   digest: Positive semidefiniteness of the midpoint moment gap kernel by integrated supporting tangents. -/

import D5.S3.Analytic.MomentMinors.Defs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.InformationTheory.KullbackLeibler.KLFun

/-! The power Jensen gaps form a positive semidefinite midpoint kernel. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open MeasureTheory Set Finset
open scoped BigOperators

namespace D5.S3.Analytic.MomentMinors.MomentKernel
open D5.S3.Analytic.MomentMinors.Defs

private def potential (s x : ℝ) : ℝ :=
  if s = 0 then x - 1 - Real.log x
  else if s = 1 then x * Real.log x - x + 1
  else (x ^ s - s * x + s - 1) / (s * (s - 1))

private def slope (s x : ℝ) : ℝ :=
  if s = 1 then Real.log x else (x ^ (s - 1) - 1) / (s - 1)

private lemma potential_hasDerivAt (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (potential s) (slope s x) x := by
  change HasDerivAt (fun y => potential s y) (slope s x) x
  by_cases hs0 : s = 0
  · subst s
    simp only [potential, slope, ↓reduceIte, zero_ne_one, zero_sub]
    convert (((hasDerivAt_id x).sub_const 1).sub (Real.hasDerivAt_log hx.ne')) using 1
    · ext y
      rfl
    · simp [Real.rpow_neg_one]
      ring
  · by_cases hs1 : s = 1
    · subst s
      simp only [potential, slope, one_ne_zero, ↓reduceIte]
      convert InformationTheory.hasDerivAt_klFun hx.ne' using 1
      exact funext fun y => (add_sub_right_comm (y * Real.log y) 1 y).symm
    · simp only [potential, slope, hs0, hs1, ↓reduceIte]
      convert (((((Real.hasDerivAt_rpow_const (p := s) (Or.inl hx.ne')).sub
        ((hasDerivAt_id x).const_mul s)).add_const s).sub_const 1).div_const
          (s * (s - 1))) using 1
      · ext y
        rfl
      · field_simp [hs0, sub_ne_zero.mpr hs1]

private lemma slope_hasDerivAt (s : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (slope s) (x ^ (s - 2)) x := by
  change HasDerivAt (fun y => slope s y) (x ^ (s - 2)) x
  by_cases hs1 : s = 1
  · subst s
    simp only [slope, ↓reduceIte]
    convert Real.hasDerivAt_log hx.ne' using 1
    norm_num [Real.rpow_neg_one]
  · simp only [slope, hs1, ↓reduceIte]
    convert ((Real.hasDerivAt_rpow_const (p := s - 1) (Or.inl hx.ne')).sub_const 1).div_const
      (s - 1) using 1
    rw [show s - 1 - 1 = s - 2 by ring]
    exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr hs1)).symm

private lemma potential_integrable {μ : Measure ℝ} {I : Set ℝ}
    (hμ : Admissible μ I) {s : ℝ} (hs : s ∈ I) :
    Integrable (potential s) μ := by
  change Integrable (fun x => potential s x) μ
  letI : IsProbabilityMeasure μ := hμ.probability
  by_cases hs0 : s = 0
  · subst s
    simp only [potential, ↓reduceIte]
    convert (hμ.integrable_id.sub (integrable_const 1)).sub (hμ.integrable_log hs) using 1
    ext x
    rfl
  · by_cases hs1 : s = 1
    · subst s
      simp only [potential, one_ne_zero, ↓reduceIte]
      convert ((hμ.integrable_mul_log hs).sub hμ.integrable_id).add (integrable_const 1) using 1
      ext x
      rfl
    · simpa only [potential, hs0, hs1, ↓reduceIte, Pi.sub_apply, Pi.add_apply, id_eq] using
        ((((hμ.integrable_rpow s hs).sub (hμ.integrable_id.const_mul s)).add
          (integrable_const s)).sub (integrable_const 1)).div_const (s * (s - 1))

private lemma lam_eq_integral_potential {μ : Measure ℝ} {I : Set ℝ}
    (hμ : Admissible μ I) {s : ℝ} (hs : s ∈ I) :
    lam μ s = (∫ x, potential s x ∂μ) - potential s (mean μ) := by
  letI : IsProbabilityMeasure μ := hμ.probability
  by_cases hs0 : s = 0
  · subst s
    simp only [lam, potential, ↓reduceIte]
    rw [integral_sub (f := fun x : ℝ => x - 1) (g := Real.log)
      (hμ.integrable_id.sub (integrable_const 1)) (hμ.integrable_log hs),
      integral_sub (f := fun x : ℝ => x) (g := fun _ => 1)
        hμ.integrable_id (integrable_const 1)]
    simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, mean]
    ring
  · by_cases hs1 : s = 1
    · subst s
      simp only [lam, potential, one_ne_zero, ↓reduceIte]
      rw [integral_add (f := fun x : ℝ => x * Real.log x - x) (g := fun _ => 1)
        ((hμ.integrable_mul_log hs).sub hμ.integrable_id) (integrable_const 1),
        integral_sub (f := fun x : ℝ => x * Real.log x) (g := fun x => x)
          (hμ.integrable_mul_log hs) hμ.integrable_id]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, mean]
      ring
    · simp only [lam, potential, hs0, hs1, ↓reduceIte]
      rw [integral_div,
        integral_sub (f := fun x : ℝ => x ^ s - s * x + s) (g := fun _ => 1)
        (((hμ.integrable_rpow s hs).sub (hμ.integrable_id.const_mul s)).add
          (integrable_const s)) (integrable_const 1),
        integral_add (f := fun x : ℝ => x ^ s - s * x) (g := fun _ => s)
        ((hμ.integrable_rpow s hs).sub (hμ.integrable_id.const_mul s))
          (integrable_const s),
        integral_sub (f := fun x : ℝ => x ^ s) (g := fun x => s * x)
          (hμ.integrable_rpow s hs) (hμ.integrable_id.const_mul s),
        integral_const_mul]
      simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_smul, mean]
      ring

/-- Every finite midpoint moment matrix of an admissible positive law is positive
semidefinite. The interval assumption supplies all intermediate power moments. -/
theorem momentKernel_posSemidef {κ : Type*} [Fintype κ]
    {I : Set ℝ} (hI : I.OrdConnected) {μ : Measure ℝ} (hμ : Admissible μ I)
    (t : κ → ℝ) (ht : ∀ i, t i ∈ I) :
    Matrix.PosSemidef (fun i j : κ => lam μ ((t i + t j) / 2)) := by
  classical
  letI : IsProbabilityMeasure μ := hμ.probability
  have hm : 0 < mean μ := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hμ.positive.mono fun _ h => h.le) hμ.integrable_id).mpr
    have hsupp : Function.support (fun x : ℝ => x) =ᵐ[μ] Set.univ :=
      hμ.positive.mono fun x hx => by simp [Function.mem_support, hx.ne']
    rw [measure_congr hsupp]
    simp
  have hmid (i j : κ) : (t i + t j) / 2 ∈ I := by
    have hh := hI.convex (𝕜 := ℝ) |>.midpoint_mem (ht i) (ht j)
    simpa only [midpoint_eq_smul_add, smul_eq_mul, invOf_eq_inv, div_eq_mul_inv,
      mul_comm] using hh
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    rw [add_comm]
  intro c
  let F : ℝ → ℝ := fun x => ∑ i, ∑ j, c i * c j * potential ((t i + t j) / 2) x
  let G : ℝ → ℝ := fun x => ∑ i, ∑ j, c i * c j * slope ((t i + t j) / 2) x
  have hF (x : ℝ) (hx : 0 < x) : HasDerivAt F (G x) x :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      (potential_hasDerivAt _ hx).const_mul _
  have hG (x : ℝ) (hx : 0 < x) :
      HasDerivAt G (∑ i, ∑ j, c i * c j * x ^ ((t i + t j) / 2 - 2)) x :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ =>
      (slope_hasDerivAt _ hx).const_mul _
  have hFconvex : ConvexOn ℝ (Ioi 0) F := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioi 0)
      (fun x hx => (hF x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hF x (interior_subset hx)).hasDerivWithinAt)
      (fun x hx => (hG x (interior_subset hx)).hasDerivWithinAt)
    intro x hx
    have hxpos : 0 < x := interior_subset hx
    have hexp (i j : κ) : x ^ ((t i + t j) / 2 - 2) =
        x ^ (t i / 2 - 1) * x ^ (t j / 2 - 1) := by
      rw [← Real.rpow_add hxpos]
      congr 1
      ring
    convert sq_nonneg (∑ i, c i * x ^ (t i / 2 - 1)) using 1
    simp only [pow_two, sum_mul, mul_sum, hexp]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  have htangent : ∀ x : ℝ, 0 < x → F (mean μ) + G (mean μ) * (x - mean μ) ≤ F x := by
    intro x hx
    rcases lt_trichotomy (mean μ) x with hmx | hmx | hxm
    · have hs := hFconvex.le_slope_of_hasDerivAt hm hx hmx (hF _ hm)
      rw [slope_def_field] at hs
      have h := (le_div_iff₀ (sub_pos.mpr hmx)).mp hs
      linarith
    · subst x
      simp
    · have hs := hFconvex.slope_le_of_hasDerivAt hx hm hxm (hF _ hm)
      rw [slope_def_field] at hs
      have h := (div_le_iff₀ (sub_pos.mpr hxm)).mp hs
      nlinarith
  have hFi : Integrable F μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (potential_integrable hμ (hmid i j)).const_mul _
  have hTi : Integrable (fun x => F (mean μ) + G (mean μ) * (x - mean μ)) μ :=
    (integrable_const _).add ((hμ.integrable_id.sub (integrable_const _)).const_mul _)
  have hbound := integral_mono_ae hTi hFi (hμ.positive.mono fun x hx => htangent x hx)
  have hT : (∫ x, F (mean μ) + G (mean μ) * (x - mean μ) ∂μ) = F (mean μ) := by
    rw [integral_add (f := fun _ : ℝ => F (mean μ))
      (g := fun x : ℝ => G (mean μ) * (x - mean μ)) (integrable_const _)
      ((hμ.integrable_id.sub (integrable_const _)).const_mul _), integral_const_mul,
      integral_sub (f := fun x : ℝ => x) (g := fun _ => mean μ)
        hμ.integrable_id (integrable_const _)]
    simp [mean]
  rw [hT] at hbound
  have hgap : (∫ x, F x ∂μ) - F (mean μ) =
      ∑ i, ∑ j, c i * c j * lam μ ((t i + t j) / 2) := by
    dsimp [F]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      (potential_integrable hμ (hmid i j)).const_mul _)]
    simp_rw [integral_finsetSum _ (fun j _ =>
      (potential_integrable hμ (hmid _ j)).const_mul _), integral_const_mul,
      lam_eq_integral_potential hμ (hmid _ _), mul_sub, sum_sub_distrib]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial, mul_sum]
  have he : (∑ i, ∑ j, c i * (lam μ ((t i + t j) / 2) * c j)) =
      ∑ i, ∑ j, c i * c j * lam μ ((t i + t j) / 2) := by
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [he, ← hgap]
  exact sub_nonneg.mpr hbound

end D5.S3.Analytic.MomentMinors.MomentKernel
