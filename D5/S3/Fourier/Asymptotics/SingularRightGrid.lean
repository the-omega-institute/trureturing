/- GID: D5/S3/Fourier/Asymptotics/SingularRightGrid
   generality: G
   mirror-B: D5/B/S3/Fourier/Asymptotics/SingularRightGrid
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Singular right-grid quadrature has a uniform square-root error for complex H1 representatives. -/

import D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem
import D5.S3.Observer.HilbertGeometry.VectorPathDerivativeIntegrability
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate

open Set MeasureTheory Filter
open scoped Topology InnerProductSpace
open D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem
open D5.S3.Observer.HilbertGeometry.VectorPathDerivativeIntegrability
open private ac_lipschitz_comp from D5.S3.Observer.HilbertGeometry.HilbertPathFundamentalTheorem

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace D5.S3.Fourier.Asymptotics.SingularRightGrid

/-- The continuous, absolutely continuous representative of a complex H1 function is used
pointwise. The derivative is the actual almost-everywhere derivative, not an arbitrary energy
certificate. The floor and its final partial interval are retained. One explicit deterministic
constant works for every function, every positive spacing h, and every endpoint h ≤ b ≤ A. -/
theorem result (A : ℝ) (hA : 0 < A) (f : ℝ → ℂ)
    (hf : AbsolutelyContinuousOnInterval f 0 A)
    (hf2 : IntervalIntegrable (fun x => ‖deriv f x‖^2) volume 0 A)
    (h b : ℝ) (hh : 0 < h) (hhb : h ≤ b) (hbA : b ≤ A) :
    |(∑ k ∈ Finset.range (Nat.floor (b/h)),
        (‖f (((k:ℝ)+1)*h)‖^2-‖f 0‖^2) / ((k:ℝ)+1)) -
      ∫ x in 0..b, (‖f x‖^2-‖f 0‖^2)/x| ≤
      14*(1/Real.sqrt A+Real.sqrt A)*Real.sqrt h*
        (∫ x in 0..A, (‖f x‖^2+‖deriv f x‖^2)) := by
  have quadrature (g : ℝ → ℝ) (A h b : ℝ) (hA : 0 < A) (hh : 0 < h) (hhb : h ≤ b) (hbA : b ≤ A)
      (hg : AbsolutelyContinuousOnInterval g 0 A) (hg0 : g 0 = 0)
      (hg2 : IntervalIntegrable (fun x => (deriv g x)^2) volume 0 A) :
      |(∑ k ∈ Finset.range (Nat.floor (b/h)), g (((k:ℝ)+1)*h) / ((k:ℝ)+1)) - ∫ x in 0..b, g x/x| ≤
        7*Real.sqrt h*Real.sqrt (∫ t in 0..A, (deriv g t)^2) := by
    have singular (g : ℝ → ℝ) (A : ℝ) (hA : 0 < A)
        (hg : AbsolutelyContinuousOnInterval g 0 A) (hg0 : g 0 = 0)
        (hg2 : IntervalIntegrable (fun x => (deriv g x)^2) volume 0 A) :
        (∀ x ∈ Icc (0:ℝ) A, |g x| ≤ Real.sqrt x * Real.sqrt (∫ t in 0..A, (deriv g t)^2)) ∧
        IntervalIntegrable (fun x => g x / x) volume 0 A ∧
        (∀ h, 0 < h → h ≤ A → |∫ x in 0..h, g x / x| ≤
          2 * Real.sqrt h * Real.sqrt (∫ t in 0..A, (deriv g t)^2)) := by
      have cauchy {a b : ℝ} (hab : a ≤ b) (d : ℝ → ℝ)
          (hd : IntervalIntegrable d volume a b)
          (hd2 : IntervalIntegrable (fun x => (d x)^2) volume a b) :
          (∫ x in a..b, |d x|) ≤ Real.sqrt (b-a) * Real.sqrt (∫ x in a..b, (d x)^2) := by
        have hm : MemLp d 2 (volume.restrict (Ioc a b)) :=
          (memLp_two_iff_integrable_sq hd.1.aestronglyMeasurable).2 hd2.1
        have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc a b))
          Real.HolderConjugate.two_two (f := fun _ : ℝ => 1) (g := fun x => |d x|)
          (ae_of_all _ (fun _ => zero_le_one)) (ae_of_all _ (fun _ => abs_nonneg _))
          (memLp_const (1 : ℝ)) (by simpa only [Real.norm_eq_abs, ENNReal.ofReal_ofNat] using hm.norm)
        simpa [intervalIntegral.integral_of_le hab, Real.rpow_two, Real.sqrt_eq_rpow,
          Real.volume_Ioc, sub_nonneg.mpr hab] using hcs
      have hd := hg.intervalIntegrable_deriv
      have bound : ∀ x ∈ Icc (0:ℝ) A,
          |g x| ≤ Real.sqrt x * Real.sqrt (∫ t in 0..A, (deriv g t)^2) := by
        intro x hx
        have sub : uIcc (0:ℝ) x ⊆ uIcc (0:ℝ) A := by
          rw [uIcc_of_le hx.1, uIcc_of_le hA.le]
          exact Icc_subset_Icc le_rfl hx.2
        have ftc := (hg.mono sub).integral_deriv_eq_sub
        rw [hg0, sub_zero] at ftc
        calc
          |g x| = ‖∫ t in 0..x, deriv g t‖ := by rw [ftc, Real.norm_eq_abs]
          _ ≤ ∫ t in 0..x, |deriv g t| := by simpa only [Real.norm_eq_abs] using intervalIntegral.norm_integral_le_integral_norm (f := deriv g) hx.1
          _ ≤ Real.sqrt (x-0) * Real.sqrt (∫ t in 0..x, (deriv g t)^2) := cauchy hx.1 _ (hd.mono_set sub) (hg2.mono_set sub)
          _ ≤ Real.sqrt x * Real.sqrt (∫ t in 0..A, (deriv g t)^2) := by
            simp only [sub_zero]
            apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
            exact intervalIntegral.integral_mono_interval le_rfl hx.1 hx.2
              (ae_of_all _ (fun _ => sq_nonneg _)) hg2
      let G := Real.sqrt (∫ t in 0..A, (deriv g t)^2)
      have hp (x : ℝ) (hx : 0 < x) : Real.sqrt x / x = x ^ (-(1/2:ℝ)) := by
        rw [show -(1/2:ℝ) = 1/2-1 by norm_num, Real.rpow_sub hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have major (x : ℝ) (hx : x ∈ Ioc (0:ℝ) A) :
          ‖g x / x‖ ≤ G * x ^ (-(1/2:ℝ)) := by
        rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx.1]
        calc
          |g x| / x ≤ (Real.sqrt x * G) / x := div_le_div_of_nonneg_right (bound x ⟨hx.1.le,hx.2⟩) hx.1.le
          _ = G * x ^ (-(1/2:ℝ)) := by rw [← hp x hx.1]; ring
      have hint : IntervalIntegrable (fun x => g x / x) volume 0 A := by
        apply IntervalIntegrable.mono_fun' ((intervalIntegral.intervalIntegrable_rpow' (by norm_num : -1 < -(1/2:ℝ))).const_mul G)
        · simp only [div_eq_mul_inv]
          exact ((hg.continuousOn.aestronglyMeasurable measurableSet_uIcc).mono_set uIoc_subset_uIcc).mul
            (measurable_inv.aestronglyMeasurable : AEStronglyMeasurable (fun x : ℝ => x⁻¹) _)
        · filter_upwards [ae_restrict_mem measurableSet_uIoc] with x hx
          exact major x (by simpa [uIoc_of_le hA.le] using hx)
      refine ⟨bound, hint, ?_⟩
      intro h hh hhA
      have hi := intervalIntegral.norm_integral_le_of_norm_le hh.le
        (ae_of_all _ (fun x (hx : x ∈ Ioc (0:ℝ) h) => major x ⟨hx.1,hx.2.trans hhA⟩))
        ((intervalIntegral.intervalIntegrable_rpow' (a:=0) (b:=h) (by norm_num : -1 < -(1/2:ℝ))).const_mul G)
      rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num : -1 < -(1/2:ℝ)))] at hi
      norm_num [Real.norm_eq_abs, ← Real.sqrt_eq_rpow] at hi
      nlinarith [hi]
    have grid (q : ℝ → ℝ) (a h : ℝ) (n : ℕ) (hh : 0 < h)
        (hq : AbsolutelyContinuousOnInterval q a (a+n*h)) :
        |(∑ k ∈ Finset.range n, h*q (a+(k+1)*h)) - ∫ x in a..a+n*h, q x| ≤
          h * ∫ x in a..a+n*h, |deriv q x| := by
      have total : a ≤ a+n*h := by linarith [mul_nonneg (Nat.cast_nonneg n) hh.le]
      have grid (k : ℕ) (hk : k < n) :
          uIcc (a+k*h) (a+(k+1)*h) ⊆ uIcc a (a+n*h) := by
        rw [uIcc_of_le (by nlinarith [hh]), uIcc_of_le total]
        have kn : (k:ℝ)+1 ≤ n := by exact_mod_cast hk
        exact Icc_subset_Icc (by linarith [mul_nonneg (Nat.cast_nonneg k) hh.le]) (by nlinarith)
      have hqi : IntervalIntegrable q volume a (a+n*h) := hq.continuousOn.intervalIntegrable
      have hdi := hq.intervalIntegrable_deriv
      have cell (k : ℕ) (hk : k ∈ Finset.range n) :
          |h*q (a+(k+1)*h) - ∫ x in a+k*h..a+(k+1)*h, q x| ≤
            h * ∫ x in a+k*h..a+(k+1)*h, |deriv q x| := by
        have hkn : k < n := Finset.mem_range.mp hk
        have sub := grid k hkn
        have ord : a+k*h ≤ a+(k+1)*h := by nlinarith
        have hc := hq.mono sub
        have hb (x : ℝ) (hx : x ∈ Icc (a+k*h) (a+(k+1)*h)) :
            ‖q (a+(k+1)*h)-q x‖ ≤ ∫ t in a+k*h..a+(k+1)*h, |deriv q t| := by
          have subx : uIcc x (a+(k+1)*h) ⊆ uIcc (a+k*h) (a+(k+1)*h) := by
            rw [uIcc_of_le hx.2, uIcc_of_le ord]
            exact Icc_subset_Icc hx.1 le_rfl
          rw [← (hc.mono subx).integral_deriv_eq_sub]
          apply (intervalIntegral.norm_integral_le_integral_norm hx.2).trans
          simpa only [Real.norm_eq_abs] using
            intervalIntegral.integral_mono_interval hx.1 hx.2 le_rfl
              (ae_of_all _ (fun _ => abs_nonneg _)) (hc.intervalIntegrable_deriv.norm)
        have he : h*q (a+(k+1)*h) - ∫ x in a+k*h..a+(k+1)*h, q x =
            ∫ x in a+k*h..a+(k+1)*h, (q (a+(k+1)*h)-q x) := by
          rw [intervalIntegral.integral_sub intervalIntegrable_const (hqi.mono_set sub), intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        rw [he]
        have hb' := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := a+k*h) (b := a+(k+1)*h) (f := fun x => q (a+(k+1)*h)-q x)
          (fun x hx => hb x (by simpa only [uIcc_of_le ord] using uIoc_subset_uIcc hx))
        rw [show a+((k:ℝ)+1)*h-(a+k*h)=h by ring, abs_of_pos hh] at hb'
        simpa only [Real.norm_eq_abs, mul_comm] using hb'
      have hsumq : (∑ k ∈ Finset.range n, ∫ x in a+k*h..a+(k+1)*h, q x) =
          ∫ x in a..a+n*h, q x := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero] using
          intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => a+k*h)
            (fun k hk => hqi.mono_set (by simpa only [Nat.cast_add, Nat.cast_one] using grid k hk))
      have hsumd : (∑ k ∈ Finset.range n, ∫ x in a+k*h..a+(k+1)*h, |deriv q x|) =
          ∫ x in a..a+n*h, |deriv q x| := by
        simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul, add_zero, Real.norm_eq_abs] using
          intervalIntegral.sum_integral_adjacent_intervals (a := fun k : ℕ => a+k*h)
            (fun k hk => hdi.norm.mono_set (by simpa only [Nat.cast_add, Nat.cast_one] using grid k hk))
      rw [← hsumq, ← Finset.sum_sub_distrib]
      calc
        _ ≤ ∑ k ∈ Finset.range n, |h*q (a+(k+1)*h) - ∫ x in a+k*h..a+(k+1)*h, q x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ k ∈ Finset.range n, h * ∫ x in a+k*h..a+(k+1)*h, |deriv q x| := Finset.sum_le_sum cell
        _ = _ := by rw [← Finset.mul_sum, hsumd]
    have weighted (g : ℝ → ℝ) (A h b G : ℝ) (hh : 0 < h) (hhb : h ≤ b) (hbA : b ≤ A)
        (hg : AbsolutelyContinuousOnInterval g 0 A)
        (hg2 : IntervalIntegrable (fun x => (deriv g x)^2) volume 0 A)
        (hG : 0 ≤ G) (hD : (∫ x in 0..A, (deriv g x)^2) ≤ G^2)
        (bound : ∀ x ∈ Icc (0:ℝ) A, |g x| ≤ Real.sqrt x * G) :
        AbsolutelyContinuousOnInterval (fun x => g x / x) h b ∧
        h * (∫ x in h..b, |deriv (fun x => g x / x) x|) ≤ 3 * Real.sqrt h * G := by
      have hA : 0 < A := hh.trans_le (hhb.trans hbA)
      have sub : uIcc h b ⊆ uIcc (0:ℝ) A := by
        rw [uIcc_of_le hhb, uIcc_of_le hA.le]
        exact Icc_subset_Icc hh.le hbA
      have hinv : ContDiffOn ℝ 1 (fun x : ℝ => x⁻¹) (uIcc h b) :=
        contDiffOn_id.inv (fun x hx => ne_of_gt (hh.trans_le (show x ∈ Icc h b by simpa only [uIcc_of_le hhb] using hx).1))
      have hiac : AbsolutelyContinuousOnInterval (fun x : ℝ => x⁻¹) h b := hinv.absolutelyContinuousOnInterval
      have hq : AbsolutelyContinuousOnInterval (fun x => g x / x) h b := by
        simpa only [div_eq_mul_inv] using (hg.mono sub).fun_mul hiac
      refine ⟨hq, ?_⟩
      have hd := hg.intervalIntegrable_deriv.mono_set sub
      have hd2 := hg2.mono_set sub
      have hci : ContinuousOn (fun x : ℝ => x⁻¹) (uIcc h b) := hinv.continuousOn
      have hwi : IntervalIntegrable (fun x => |deriv g x| / x) volume h b := by
        simpa only [div_eq_mul_inv, Real.norm_eq_abs] using hd.norm.mul_continuousOn hci
      have hpi : IntervalIntegrable (fun x : ℝ => x ^ (-(3/2:ℝ))) volume h b :=
        intervalIntegral.intervalIntegrable_rpow (Or.inr (by rw [uIcc_of_le hhb]; exact fun hx => (not_le.mpr hh) hx.1))
      have hdsq : (∫ x in h..b, (deriv g x)^2) ≤ G^2 :=
        (intervalIntegral.integral_mono_interval hh.le hhb hbA
          (ae_of_all _ (fun _ => sq_nonneg _)) hg2).trans hD
      have hinvsq : (∫ x in h..b, (x⁻¹)^2) ≤ h⁻¹ := by
        have he : (∫ x in h..b, (x⁻¹)^2) = h⁻¹-b⁻¹ := by
          have hc : IntervalIntegrable (fun x : ℝ => -(x⁻¹)^2) volume h b :=
            (hci.pow 2).neg.intervalIntegrable
          have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := h) (b := b)
            (fun x hx => by simpa only [inv_pow] using hasDerivAt_inv (ne_of_gt (hh.trans_le (show x ∈ Icc h b by simpa only [uIcc_of_le hhb] using hx).1))) hc
          simpa only [intervalIntegral.integral_neg, neg_eq_iff_eq_neg, neg_sub] using hf
        rw [he]
        exact sub_le_self _ (inv_nonneg.mpr (hh.le.trans hhb))
      have hcs : (∫ x in h..b, |deriv g x| / x) ≤ G / Real.sqrt h := by
        have hm : MemLp (deriv g) 2 (volume.restrict (Ioc h b)) :=
          (memLp_two_iff_integrable_sq hd.1.aestronglyMeasurable).2 hd2.1
        have him : MemLp (fun x : ℝ => x⁻¹) 2 (volume.restrict (Ioc h b)) :=
          (memLp_two_iff_integrable_sq (hci.intervalIntegrable (μ := volume)).1.aestronglyMeasurable).2
            (hci.pow 2).intervalIntegrable.1
        have hhcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc h b))
          Real.HolderConjugate.two_two
          (f := fun x => |deriv g x|) (g := fun x : ℝ => x⁻¹)
          (ae_of_all _ (fun _ => abs_nonneg _))
          (ae_restrict_of_forall_mem measurableSet_Ioc (fun x hx => inv_nonneg.mpr (hh.le.trans hx.1.le)))
          (by simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hm.norm)
          (by simpa only [ENNReal.ofReal_ofNat] using him)
        have H : (∫ x in h..b, |deriv g x| / x) ≤
            Real.sqrt (∫ x in h..b, (deriv g x)^2) * Real.sqrt (∫ x in h..b, (x⁻¹)^2) := by
          simpa [intervalIntegral.integral_of_le hhb, Real.rpow_two, Real.sqrt_eq_rpow, div_eq_mul_inv] using hhcs
        calc
          _ ≤ Real.sqrt (∫ x in h..b, (deriv g x)^2) * Real.sqrt (∫ x in h..b, (x⁻¹)^2) := H
          _ ≤ G * Real.sqrt (h⁻¹) := mul_le_mul
            (by simpa only [Real.sqrt_sq hG] using Real.sqrt_le_sqrt hdsq)
            (Real.sqrt_le_sqrt hinvsq) (Real.sqrt_nonneg _) hG
          _ = G / Real.sqrt h := by rw [Real.sqrt_inv, div_eq_mul_inv]
      have hpint : (∫ x in h..b, x ^ (-(3/2:ℝ))) ≤ 2 / Real.sqrt h := by
        rw [integral_rpow (Or.inr ⟨by norm_num, by rw [uIcc_of_le hhb]; exact fun hx => (not_le.mpr hh) hx.1⟩)]
        norm_num
        rw [Real.rpow_neg (hh.le.trans hhb), Real.rpow_neg hh.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        have : 0 ≤ (Real.sqrt b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg b)
        simp only [div_eq_mul_inv]
        nlinarith
      have hder : ∀ᵐ x, x ∈ uIcc h b → deriv (fun x => g x / x) x =
          deriv g x / x - g x / x^2 := by
        filter_upwards [hg.ae_differentiableAt] with x hx hxhb
        have hx0 : x ≠ 0 := ne_of_gt (hh.trans_le (show x ∈ Icc h b by simpa only [uIcc_of_le hhb] using hxhb).1)
        have H := ((hx (sub hxhb)).hasDerivAt.fun_div (hasDerivAt_id x) hx0).deriv
        simp only [id_eq, mul_one] at H
        rw [H]
        field_simp
      have he : (∫ x in h..b, |deriv (fun x => g x / x) x|) ≤
          (∫ x in h..b, |deriv g x| / x) + G * (∫ x in h..b, x ^ (-(3/2:ℝ))) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hwi (hpi.const_mul G)]
        apply intervalIntegral.integral_mono_ae_restrict hhb hq.intervalIntegrable_deriv.norm (hwi.add (hpi.const_mul G))
        filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hder] with x hxmem hx
        have hx0 : 0 < x := hh.trans_le hxmem.1
        exact (by
          rw [show ‖deriv (fun x => g x / x) x‖ = |deriv (fun x => g x / x) x| from Real.norm_eq_abs _, hx (by simpa [uIcc_of_le hhb] using hxmem)]
          calc
            _ ≤ |deriv g x / x| + |g x / x^2| := abs_sub _ _
            _ ≤ |deriv g x| / x + (Real.sqrt x * G) / x^2 := by
              rw [abs_div, abs_div, abs_of_pos hx0, abs_of_nonneg (sq_nonneg x)]
              exact add_le_add_right (div_le_div_of_nonneg_right (bound x ⟨hx0.le,hxmem.2.trans hbA⟩) (sq_nonneg x)) _
            _ = |deriv g x| / x + G * x ^ (-(3/2:ℝ)) := by
              congr 1
              rw [show -(3/2:ℝ) = 1/2-2 by norm_num, Real.rpow_sub hx0, Real.rpow_two, ← Real.sqrt_eq_rpow]
              ring)
      have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
      have he' : (∫ x in h..b, |deriv (fun x => g x / x) x|) ≤ 3*G/Real.sqrt h := by
        calc
          _ ≤ _ := he
          _ ≤ G / Real.sqrt h + G * (2 / Real.sqrt h) := add_le_add hcs (mul_le_mul_of_nonneg_left hpint hG)
          _ = _ := by ring
      have ht := mul_le_mul_of_nonneg_left he' hh.le
      have heq : h*(3*G/Real.sqrt h) = 3*Real.sqrt h*G := by
        have H := Real.sq_sqrt hh.le
        field_simp
        nlinarith
      exact ht.trans_eq heq
    obtain ⟨bound, hint, small⟩ := singular g A hA hg hg0 hg2
    let G := Real.sqrt (∫ t in 0..A, (deriv g t)^2)
    have hE : 0 ≤ ∫ t in 0..A, (deriv g t)^2 :=
      intervalIntegral.integral_nonneg_of_forall hA.le (fun _ => sq_nonneg _)
    have hG : 0 ≤ G := Real.sqrt_nonneg _
    have hD : (∫ t in 0..A, (deriv g t)^2) ≤ G^2 := by dsimp [G]; rw [Real.sq_sqrt hE]
    have hfloor : 0 < Nat.floor (b/h) := Nat.floor_pos.mpr ((le_div_iff₀ hh).mpr (by simpa using hhb))
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hfloor)
    have hc : ((m:ℝ)+1)*h ≤ b := by
      have H := (le_div_iff₀ hh).mp (Nat.floor_le (div_nonneg (hh.le.trans hhb) hh.le))
      simpa only [hm, Nat.cast_succ] using H
    have hbc : b < ((m:ℝ)+2)*h := by
      have H := (div_lt_iff₀ hh).mp (Nat.lt_floor_add_one (b/h))
      simpa only [hm, Nat.cast_succ, add_assoc, one_add_one_eq_two] using H
    let c := ((m:ℝ)+1)*h
    have hhc : h ≤ c := by dsimp [c]; nlinarith [mul_nonneg (Nat.cast_nonneg m) hh.le]
    have hcA : c ≤ A := hc.trans hbA
    have hq := weighted g A h c G hh hhc hcA hg hg2 hG hD bound
    have hgri := grid (fun x => g x/x) h h m hh (by convert hq.1 using 1 <;> dsimp [c] <;> ring)
    have hmain : |(∑ k ∈ Finset.range m, g (((k:ℝ)+2)*h) / ((k:ℝ)+2)) - ∫ x in h..c, g x/x| ≤
        3*Real.sqrt h*G := by
      have hs : (∑ k ∈ Finset.range m, h * (g (h+(k+1)*h)/(h+(k+1)*h))) =
          ∑ k ∈ Finset.range m, g (((k:ℝ)+2)*h) / ((k:ℝ)+2) := by
        apply Finset.sum_congr rfl
        intro k hk
        have H : h+((k:ℝ)+1)*h = ((k:ℝ)+2)*h := by ring
        rw [H]
        field_simp
      rw [hs, show h+(m:ℝ)*h=c by dsimp [c]; ring] at hgri
      exact hgri.trans hq.2
    have htail : |∫ x in c..b, g x/x| ≤ Real.sqrt h*G := by
      have H := intervalIntegral.norm_integral_le_of_norm_le_const (a:=c) (b:=b)
        (f := fun x => g x/x) (C := G/Real.sqrt h) (fun x hx => by
          have hx' : x ∈ Ioc c b := by simpa only [uIoc_of_le (show c ≤ b from hc)] using hx
          have hx0 : 0 < x := hh.trans_le (hhc.trans hx'.1.le)
          rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0]
          have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
          calc
            |g x|/x ≤ (Real.sqrt x*G)/x := div_le_div_of_nonneg_right (bound x ⟨hx0.le,hx'.2.trans hbA⟩) hx0.le
            _ = G/Real.sqrt x := by field_simp; nlinarith [Real.sq_sqrt hx0.le]
            _ ≤ G/Real.sqrt h := div_le_div_of_nonneg_left hG (Real.sqrt_pos.mpr hh) (Real.sqrt_le_sqrt (hhc.trans hx'.1.le)))
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hc)] at H
      calc
        _ ≤ G/Real.sqrt h*(b-c) := H
        _ ≤ G/Real.sqrt h*h := mul_le_mul_of_nonneg_left (by dsimp [c]; nlinarith) (div_nonneg hG (Real.sqrt_nonneg _))
        _ = Real.sqrt h*G := by
          have hs : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh
          field_simp
          nlinarith [Real.sq_sqrt hh.le]
    have intsub {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ A) :
        IntervalIntegrable (fun x => g x/x) volume u v := by
      apply hint.mono_set
      rw [uIcc_of_le huv, uIcc_of_le hA.le]
      exact Icc_subset_Icc hu hv
    have he : (∫ x in 0..b, g x/x) = (∫ x in 0..h, g x/x) +
        (∫ x in h..c, g x/x) + ∫ x in c..b, g x/x := by
      rw [intervalIntegral.integral_add_adjacent_intervals (intsub le_rfl hh.le (hhb.trans hbA)) (intsub hh.le hhc hcA),
        intervalIntegral.integral_add_adjacent_intervals (intsub le_rfl (hh.le.trans hhc) hcA) (intsub (hh.le.trans hhc) hc hbA)]
    rw [hm, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, one_mul, div_one, Nat.cast_add, Nat.cast_one]
    simp_rw [add_assoc, one_add_one_eq_two]
    rw [he]
    have hzero := bound h ⟨hh.le, hhb.trans hbA⟩
    have hsmall := small h hh (hhb.trans hbA)
    calc
      _ = |g h - (∫ x in 0..h, g x/x) +
          ((∑ k ∈ Finset.range m, g (((k:ℝ)+2)*h) / ((k:ℝ)+2)) - ∫ x in h..c, g x/x) -
          ∫ x in c..b, g x/x| := by congr 1; ring
      _ ≤ |g h| + |∫ x in 0..h, g x/x| +
          |(∑ k ∈ Finset.range m, g (((k:ℝ)+2)*h) / ((k:ℝ)+2)) - ∫ x in h..c, g x/x| +
          |∫ x in c..b, g x/x| := by
        exact (abs_sub _ _).trans (add_le_add ( (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)) le_rfl)
      _ ≤ 7*Real.sqrt h*G := by dsimp [G] at *; linarith
  have squared (f : ℝ → ℂ) (A : ℝ) (hA : 0 < A)
      (hf : AbsolutelyContinuousOnInterval f 0 A)
      (hf2 : IntervalIntegrable (fun x => ‖deriv f x‖^2) volume 0 A) :
      let g := fun x => ‖f x‖^2-‖f 0‖^2
      AbsolutelyContinuousOnInterval g 0 A ∧ g 0 = 0 ∧
      IntervalIntegrable (fun x => (deriv g x)^2) volume 0 A ∧
      Real.sqrt (∫ x in 0..A, (deriv g x)^2) ≤
        2*(1/Real.sqrt A+Real.sqrt A)*(∫ x in 0..A, (‖f x‖^2+‖deriv f x‖^2)) := by
    intro g
    let E := ∫ x in 0..A, (‖f x‖^2+‖deriv f x‖^2)
    let K := 1/Real.sqrt A+Real.sqrt A
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hfi : IntervalIntegrable (fun x => ‖f x‖^2) volume 0 A := (hf.continuousOn.norm.pow 2).intervalIntegrable
    have hei : IntervalIntegrable (fun x => ‖f x‖^2+‖deriv f x‖^2) volume 0 A := hfi.add hf2
    have hE : 0 ≤ E := intervalIntegral.integral_nonneg_of_forall hA.le (fun x => add_nonneg (sq_nonneg _) (sq_nonneg _))
    have hF : (∫ x in 0..A, ‖f x‖^2) ≤ E :=
      intervalIntegral.integral_mono_on hA.le hfi hei (fun x _ => le_add_of_nonneg_right (sq_nonneg _))
    have hD : (∫ x in 0..A, ‖deriv f x‖^2) ≤ E :=
      intervalIntegral.integral_mono_on hA.le hf2 hei (fun x _ => le_add_of_nonneg_left (sq_nonneg _))
    have hd := absolutely_continuous_interval_integrable_deriv hf
    have cs (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ A) :
        ‖f v-f u‖ ≤ Real.sqrt (v-u)*Real.sqrt E := by
      have sub : uIcc u v ⊆ uIcc (0:ℝ) A := by
        rw [uIcc_of_le huv,uIcc_of_le hA.le]
        exact Icc_subset_Icc hu hv
      have hm : MemLp (fun x => ‖deriv f x‖) 2 (volume.restrict (Ioc u v)) :=
        (memLp_two_iff_integrable_sq (hd.mono_set sub).1.norm.aestronglyMeasurable).2 (hf2.mono_set sub).1
      have hcs := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Ioc u v))
        Real.HolderConjugate.two_two (f := fun _ : ℝ => 1) (g := fun x => ‖deriv f x‖)
        (ae_of_all _ (fun _ => zero_le_one)) (ae_of_all _ (fun _ => norm_nonneg _))
        (memLp_const (1:ℝ)) (by simpa only [ENNReal.ofReal_ofNat] using hm)
      have HC : (∫ x in u..v, ‖deriv f x‖) ≤ Real.sqrt (v-u) * Real.sqrt (∫ x in u..v, ‖deriv f x‖^2) := by
        simpa [intervalIntegral.integral_of_le huv, Real.rpow_two, Real.sqrt_eq_rpow,
          Real.volume_Ioc, sub_nonneg.mpr huv] using hcs
      have ftc := absolutely_continuous_interval_integral_deriv_eq_sub (hf.mono sub) right_mem_uIcc
      rw [← ftc]
      apply ((intervalIntegral.norm_integral_le_integral_norm huv).trans HC).trans
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      exact (intervalIntegral.integral_mono_interval hu huv hv (ae_of_all _ (fun _ => sq_nonneg _)) hf2).trans hD
    have bound : ∀ x ∈ Icc (0:ℝ) A, ‖f x‖ ≤ K*Real.sqrt E := by
      obtain ⟨c,hc,havg⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
        (μ := volume) (f := fun x => ‖f x‖^2) (g := fun _ => 1)
        (hf.continuousOn.norm.pow 2) intervalIntegrable_const (fun _ _ => zero_le_one)
      have hc' : c ∈ Icc (0:ℝ) A := by simpa only [uIcc_of_le hA.le] using hc
      have havg' : (∫ x in 0..A, ‖f x‖^2) = ‖f c‖^2*A := by simpa using havg
      have hfc : ‖f c‖ ≤ Real.sqrt (E/A) :=
        (Real.le_sqrt (norm_nonneg _) (div_nonneg hE hA.le)).mpr ((le_div_iff₀ hA).mpr (havg' ▸ hF))
      intro x hx
      have hdiff : ‖f x-f c‖ ≤ Real.sqrt A*Real.sqrt E := by
        rcases le_total c x with hcx | hxc
        · exact (cs c x hc'.1 hcx hx.2).trans
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hx.2,hc'.1])) (Real.sqrt_nonneg _))
        · rw [norm_sub_rev]
          exact (cs x c hx.1 hxc hc'.2).trans
            (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by linarith [hc'.2,hx.1])) (Real.sqrt_nonneg _))
      calc
        ‖f x‖ ≤ ‖f c‖+‖f x-f c‖ := by simpa only [add_sub_cancel] using norm_add_le (f c) (f x-f c)
        _ ≤ Real.sqrt (E/A)+Real.sqrt A*Real.sqrt E := add_le_add hfc hdiff
        _ = K*Real.sqrt E := by rw [Real.sqrt_div hE]; dsimp [K]; ring
    have hre : AbsolutelyContinuousOnInterval (fun x => (f x).re) 0 A := ac_lipschitz_comp hf Complex.reCLM.lipschitz
    have him : AbsolutelyContinuousOnInterval (fun x => (f x).im) 0 A := ac_lipschitz_comp hf Complex.imCLM.lipschitz
    have hg : AbsolutelyContinuousOnInterval g 0 A := by
      have hn := (hre.fun_mul hre).fun_add (him.fun_mul him)
      have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => ‖f 0‖^2) 0 A := contDiffOn_const.absolutelyContinuousOnInterval
      simpa only [g, Complex.sq_norm, Complex.normSq_apply] using hn.fun_sub hc
    have hder : ∀ᵐ x, x ∈ uIcc (0:ℝ) A → deriv g x = 2*⟪f x,deriv f x⟫_ℝ := by
      filter_upwards [absolutely_continuous_interval_ae_hasDerivAt hf] with x hx hmem
      exact ((hx hmem).norm_sq.sub_const _).deriv
    have major : ∀ᵐ x ∂volume.restrict (uIoc (0:ℝ) A),
        |deriv g x| ≤ 2*(K*Real.sqrt E)*‖deriv f x‖ := by
      filter_upwards [ae_restrict_mem measurableSet_uIoc,ae_restrict_of_ae hder] with x hx hdg
      rw [hdg (uIoc_subset_uIcc hx), abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      rw [mul_assoc (2:ℝ)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact (abs_real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (bound x (by simpa only [uIcc_of_le hA.le] using uIoc_subset_uIcc hx)) (norm_nonneg _))
    have maj2 : ∀ᵐ x ∂volume.restrict (uIoc (0:ℝ) A),
        ‖(deriv g x)^2‖ ≤ (2*(K*Real.sqrt E))^2*‖deriv f x‖^2 := by
      filter_upwards [major] with x hx
      simpa only [norm_pow,Real.norm_eq_abs,sq_abs,mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hx 2
    have hg2 : IntervalIntegrable (fun x => (deriv g x)^2) volume 0 A :=
      IntervalIntegrable.mono_fun' (hf2.const_mul ((2*(K*Real.sqrt E))^2))
        (hg.intervalIntegrable_deriv.aestronglyMeasurable_restrict_uIoc.pow 2) maj2
    refine ⟨hg,by simp [g],hg2,?_⟩
    have hgi : (∫ x in 0..A, (deriv g x)^2) ≤ (2*(K*Real.sqrt E))^2*E := by
      calc
        _ ≤ ∫ x in 0..A, (2*(K*Real.sqrt E))^2*‖deriv f x‖^2 := by
          apply intervalIntegral.integral_mono_ae_restrict hA.le hg2 (hf2.const_mul _)
          rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
          have H : ∀ᵐ x ∂volume.restrict (Ioc (0:ℝ) A),
              ‖(deriv g x)^2‖ ≤ (2*(K*Real.sqrt E))^2*‖deriv f x‖^2 := by
            simpa only [uIoc_of_le hA.le] using maj2
          filter_upwards [H] with x hx
          simpa only [norm_pow,Real.norm_eq_abs,sq_abs] using hx
        _ = (2*(K*Real.sqrt E))^2*(∫ x in 0..A, ‖deriv f x‖^2) := intervalIntegral.integral_const_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hD (sq_nonneg _)
    have heq : (2*(K*Real.sqrt E))^2*E = (2*K*E)^2 := by
      simp only [mul_pow,Real.sq_sqrt hE]
      ring
    rw [heq] at hgi
    simpa only [Real.sqrt_sq (by positivity : 0 ≤ 2*K*E)] using Real.sqrt_le_sqrt hgi
  obtain ⟨hg,hg0,hg2,hbound⟩ := squared f A hA hf hf2
  have H := quadrature (fun x => ‖f x‖^2-‖f 0‖^2) A h b hA hh hhb hbA hg hg0 hg2
  exact H.trans ((mul_le_mul_of_nonneg_left hbound (by positivity : 0 ≤ 7*Real.sqrt h)).trans_eq (by ring))

#print axioms result
end D5.S3.Fourier.Asymptotics.SingularRightGrid
