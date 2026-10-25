import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped Interval

namespace CFMPAffineRadialEdgeLength435Transient

-- Scalar normalization for an actual affine radial geodesic edge.
theorem affine_radial_speed_integral (a b chi : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hchi : 1 < chi) :
    (∫ r : ℝ in (0 : ℝ)..1,
      a*b*Real.sqrt (chi^2-1) /
        (a^2*(1-r)^2 + 2*a*b*chi*r*(1-r) + b^2*r^2)) =
      Real.arcosh chi := by
  let w := Real.sqrt (chi^2-1)
  have hrad : 0 < chi^2-1 := by nlinarith
  have hw : 0 < w := Real.sqrt_pos.mpr hrad
  have hwsq : w^2 = chi^2-1 := Real.sq_sqrt hrad.le
  have hwm : w < chi := by nlinarith
  have hplus : 0 < chi+w := by linarith
  have hminus : 0 < chi-w := sub_pos.mpr hwm
  let p : ℝ → ℝ := fun r => a*(1-r)+b*(chi+w)*r
  let m : ℝ → ℝ := fun r => a*(1-r)+b*(chi-w)*r
  let Q : ℝ → ℝ := fun r =>
    a^2*(1-r)^2 + 2*a*b*chi*r*(1-r) + b^2*r^2
  have hpm (r : ℝ) : p r*m r = Q r := by
    dsimp only [p,m,Q]
    linear_combination -(b*r)^2 * hwsq
  have haff (k : ℝ) (hk : 0 < k) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      0 < a*(1-r)+k*r := by
    by_cases hz : r = 0
    · simpa [hz] using ha
    · exact add_pos_of_nonneg_of_pos
        (mul_nonneg ha.le (sub_nonneg.mpr hr.2))
        (mul_pos hk (lt_of_le_of_ne hr.1 (Ne.symm hz)))
  have hp (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 0 < p r :=
    haff (b*(chi+w)) (mul_pos hb hplus) r hr
  have hm (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 0 < m r :=
    haff (b*(chi-w)) (mul_pos hb hminus) r hr
  have hQ (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) : 0 < Q r := by
    rw [← hpm]
    exact mul_pos (hp r hr) (hm r hr)
  let theta : ℝ → ℝ := fun r => (Real.log (p r)-Real.log (m r))/2
  have hd (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) :
      HasDerivAt theta (a*b*w / Q r) r := by
    have hp' : HasDerivAt p (-a+b*(chi+w)) r := by
      convert ((hasDerivAt_const r a).mul ((hasDerivAt_const r (1 : ℝ)).sub
        (hasDerivAt_id r))).add ((hasDerivAt_id r).const_mul (b*(chi+w))) using 1 <;>
        (try funext t) <;> simp [p] <;> ring
    have hm' : HasDerivAt m (-a+b*(chi-w)) r := by
      convert ((hasDerivAt_const r a).mul ((hasDerivAt_const r (1 : ℝ)).sub
        (hasDerivAt_id r))).add ((hasDerivAt_id r).const_mul (b*(chi-w))) using 1 <;>
        (try funext t) <;> simp [m] <;> ring
    have h := ((hp'.log (hp r hr).ne').sub (hm'.log (hm r hr).ne')).div_const 2
    convert h using 1
    rw [← hpm]
    field_simp [(hp r hr).ne',(hm r hr).ne']
    <;> dsimp [p,m]
    <;> ring
  have hc : ContinuousOn theta (Icc (0 : ℝ) 1) :=
    fun r hr => (hd r hr).continuousAt.continuousWithinAt
  have hspeed : ContinuousOn (fun r => a*b*w/Q r) (Icc (0 : ℝ) 1) :=
    continuousOn_const.div (by unfold Q;fun_prop) (fun r hr => (hQ r hr).ne')
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (0 : ℝ) ≤ 1 by norm_num) hc
    (fun r hr => hd r ⟨hr.1.le,hr.2.le⟩)
    (ContinuousOn.intervalIntegrable_of_Icc (by norm_num) hspeed)
  have hzero : theta 0 = 0 := by simp [theta,p,m]
  have hinv : chi-w = (chi+w)⁻¹ := by
    simpa only [w] using (Real.add_sqrt_self_sq_sub_one_inv hchi.le).symm
  have hone : theta 1 = Real.arcosh chi := by
    change (Real.log (a*(1-1)+b*(chi+w)*1)-
      Real.log (a*(1-1)+b*(chi-w)*1))/2 = Real.log (chi+w)
    simp only [sub_self,mul_zero,zero_add,mul_one]
    rw [Real.log_mul hb.ne' hplus.ne',Real.log_mul hb.ne' hminus.ne',hinv,Real.log_inv]
    ring
  rw [hzero,hone,sub_zero] at hftc
  exact hftc

end CFMPAffineRadialEdgeLength435Transient

run_cmd do
  let name := ``CFMPAffineRadialEdgeLength435Transient.affine_radial_speed_integral
  let env := (← Lean.getEnv).setExporting false
  unless (env.checked.get.find? name).isSome do
    Lean.throwError m!"CFMP448 missing declaration {name}"
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
      Lean.throwError m!"CFMP448 disallowed axiom {ax}"
  Lean.logInfo m!"CFMP448 CHECKED {name} axioms={axioms}"
