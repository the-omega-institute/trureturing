/- GID: D5/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial
   generality: I
   mirror-B: D5/B/S3/Arith/Robin/PrimePrefixCurvatureVolterraFactorial
   mirror-E: none(waiver:analytic-inequality)
   anchors: []
   utility: none
   digest: The actual positive Volterra residual has its exact 3n-factorial error bound and recovers the literal curvature uniformly on every nonnegative compact interval. -/

import D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraRecursion
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-!
The literal curvature, approximations and residuals are those of
PrimePrefixCurvatureVolterraRecursion, whose public result is consumed.
A continuous integral model agrees with the same actual curvature on the
nonnegative axis; it supplies integrability without duplicating the original
all-real rate and curvature derivative chain.

The private integral_Icc_factorial_tail helper below is copied from
OpenAI math contributors, https://github.com/openai/math,
lean/OAI/Analysis/VlasovMaxwell/Regularity/VolterraSup.lean,
revision adc7f1241b42e322a6451854ab7e4b4c146bf78a, under the
Apache License, Version 2.0. Its proof body is unchanged apart from private
visibility. No copyright or author line occurs in the upstream leaf.
The helper is consumed twice for the exact lift primitive and once for the
actual Volterra estimate. No upstream general uniform-operator claim is used.

The private finite-integral continuity and nonnegative-axis congruence bodies
retain PrimePrefixCurvatureVolterraRecursion provenance. The new induction
and consumers retain the exact constant 2*3^n*(3*n)! at every finite n.
Only an auxiliary limit comparison uses n! <= (3*n)!; the public estimate
never replaces its exact factorial. The signed Robin arithmetic transport
and RH endpoint remain open.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set Filter MeasureTheory
open scoped Topology Interval
open D5.S3.Arith.Robin.PrimorialGlobalLaplaceEnvelope
open D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraRecursion

namespace D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraFactorial

private theorem integral_Icc_factorial_tail (C : ℝ) (n : ℕ) {t : ℝ} (ht : 0≤t) :
    C*(∫ u in Icc (0:ℝ) t, (C*u)^n/(n.factorial:ℝ))=
      (C*t)^(n+1)/((n+1).factorial:ℝ) := by
  have he : (fun u : ℝ => (C*u)^n/(n.factorial:ℝ))=
      (fun u => (C^n/(n.factorial:ℝ))*u^n) := by funext u; simp only [mul_pow]; ring
  rw [he,integral_const_mul,integral_Icc_eq_integral_Ioc,
    ←intervalIntegral.integral_of_le ht,integral_pow]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,zero_pow (Nat.succ_ne_zero n),sub_zero,mul_pow]
  field_simp
  ring

private theorem integral_factorial (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    (∫ t in (0 : ℝ)..v, t^n/(n.factorial : ℝ)) =
      v^(n+1)/((n+1).factorial : ℝ) := by
  have h := integral_Icc_factorial_tail 1 n hv
  simpa only [one_mul, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hv] using h

private theorem continuous_lift {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (lift f) := by
  unfold lift
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => (p.1-p.2)*f p.2) by fun_prop)
    continuous_id

private theorem continuous_volterra {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (volterra f) := by
  unfold volterra
  apply (Real.continuous_exp.comp continuous_neg).mul
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => coefficient p.2*lift f p.2) from
      (PrimePrefixCurvatureVolterraRecursion.result.1.comp continuous_snd).mul
        ((continuous_lift hf).comp continuous_snd))
    continuous_id

private theorem volterra_congr_nonnegative {f g : ℝ → ℝ}
    (hfg : ∀ v : ℝ, 0 ≤ v → f v = g v) {v : ℝ} (hv : 0 ≤ v) :
    volterra f v = volterra g v := by
  unfold volterra lift
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le hv
  intro s hs
  change coefficient s*(∫ t in (0 : ℝ)..s, (s-t)*f t) =
    coefficient s*(∫ t in (0 : ℝ)..s, (s-t)*g t)
  apply congrArg (fun x : ℝ => coefficient s*x)
  apply intervalIntegral.integral_congr_Ioo_of_le hs.1.le
  intro t ht
  change (s-t)*f t = (s-t)*g t
  rw [hfg t ht.1.le]

private def model (v : ℝ) : ℝ := Real.exp (-v)*
  (1/2 + ∫ s in (0 : ℝ)..v, coefficient s*actualPhi s)

private theorem continuous_model : Continuous model := by
  have hphi : Continuous actualPhi := continuous_iff_continuousAt.mpr
    (fun v => (hasDerivAt_actualPhi v).continuousAt)
  unfold model
  apply (Real.continuous_exp.comp continuous_neg).mul
  apply continuous_const.add
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    (show Continuous (fun p : ℝ × ℝ => coefficient p.2*actualPhi p.2) from
      (PrimePrefixCurvatureVolterraRecursion.result.1.comp continuous_snd).mul
        (hphi.comp continuous_snd))
    continuous_id

private theorem model_eq {v : ℝ} (hv : 0 ≤ v) : model v = curvature v :=
  (PrimePrefixCurvatureVolterraRecursion.result.2.2.2.1 v hv).2.1.symm

private def modelResidual (n : ℕ) : ℝ → ℝ := volterra^[n] model

private theorem modelResidual_step (n : ℕ) :
    modelResidual (n+1) = volterra (modelResidual n) :=
  Function.iterate_succ_apply' volterra n model

private theorem continuous_modelResidual (n : ℕ) : Continuous (modelResidual n) := by
  induction n with
  | zero => exact continuous_model
  | succ n ih => rw [modelResidual_step]; exact continuous_volterra ih

private theorem modelResidual_eq_iterate (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    modelResidual n v = (volterra^[n] curvature) v := by
  induction n generalizing v with
  | zero => exact model_eq hv
  | succ n ih =>
    rw [modelResidual_step, Function.iterate_succ_apply']
    exact volterra_congr_nonnegative (fun t ht => ih ht) hv

private theorem modelResidual_eq (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    modelResidual n v = residual n v := by
  rw [modelResidual_eq_iterate n hv]
  exact (PrimePrefixCurvatureVolterraRecursion.result.2.2.2.2.1 n v hv).symm

private theorem curvature_bounds {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ curvature v ∧ curvature v ≤ 1/2 := by
  rcases hv.eq_or_lt with h | h
  · subst v
    change 0 ≤ deriv (deriv actualPhi) 0 ∧ deriv (deriv actualPhi) 0 ≤ 1/2
    rw [PrimePrefixPhiCurvature.result.1]
    norm_num
  · exact ⟨(PrimePrefixPhiCurvature.result.2.2 v h).1.le,
      (PrimePrefixPhiCurvature.result.2.2 v h).2.le⟩

private theorem lift_nonnegative {f : ℝ → ℝ}
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ lift f v := by
  unfold lift
  exact intervalIntegral.integral_nonneg hv
    (fun t ht => mul_nonneg (sub_nonneg.mpr ht.2) (hpos t ht.1))

private theorem volterra_nonnegative {f : ℝ → ℝ}
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ volterra f v := by
  unfold volterra
  apply mul_nonneg (Real.exp_pos _).le
  exact intervalIntegral.integral_nonneg hv (fun s hs =>
    mul_nonneg (PrimePrefixCurvatureVolterraRecursion.result.2.2.1 s hs.1).1.le
      (lift_nonnegative hpos hs.1))

private theorem modelResidual_nonnegative (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ modelResidual n v := by
  induction n generalizing v with
  | zero => rw [modelResidual_eq 0 hv]; simpa [PrimePrefixCurvatureVolterraRecursion.residual, approximation] using (curvature_bounds hv).1
  | succ n ih => rw [modelResidual_step]; exact volterra_nonnegative (fun t ht => ih ht) hv

private theorem lift_factorial (d : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    lift (fun t : ℝ => t^d/(d.factorial : ℝ)) v =
      v^(d+2)/((d+2).factorial : ℝ) := by
  have hfun : (fun t : ℝ => (v-t)*(t^d/(d.factorial : ℝ))) =
      (fun t : ℝ => v*(t^d/(d.factorial : ℝ)) -
        (d+1 : ℝ)*(t^(d+1)/((d+1).factorial : ℝ))) := by
    funext t
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
    field_simp
  have h₁ : IntervalIntegrable (fun t : ℝ => v*(t^d/(d.factorial : ℝ))) volume 0 v :=
    (show Continuous (fun t : ℝ => v*(t^d/(d.factorial : ℝ))) by fun_prop).intervalIntegrable 0 v
  have h₂ : IntervalIntegrable (fun t : ℝ => (d+1 : ℝ)*(t^(d+1)/((d+1).factorial : ℝ))) volume 0 v :=
    (show Continuous (fun t : ℝ => (d+1 : ℝ)*(t^(d+1)/((d+1).factorial : ℝ))) by fun_prop).intervalIntegrable 0 v
  unfold lift
  rw [hfun, intervalIntegral.integral_sub h₁ h₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_factorial d hv, integral_factorial (d+1) hv]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

private theorem lift_bound {f : ℝ → ℝ} (hf : Continuous f) (d : ℕ) (M : ℝ)
    (hbound : ∀ t : ℝ, 0 ≤ t → f t ≤ M*(t^d/(d.factorial : ℝ)))
    {v : ℝ} (hv : 0 ≤ v) :
    lift f v ≤ M*(v^(d+2)/((d+2).factorial : ℝ)) := by
  have h₁ : IntervalIntegrable (fun t : ℝ => (v-t)*f t) volume 0 v :=
    ((continuous_const.sub continuous_id).mul hf).intervalIntegrable 0 v
  have h₂ : IntervalIntegrable (fun t : ℝ => (v-t)*(M*(t^d/(d.factorial : ℝ)))) volume 0 v :=
    (show Continuous (fun t : ℝ => (v-t)*(M*(t^d/(d.factorial : ℝ)))) by fun_prop).intervalIntegrable 0 v
  have hcmp := intervalIntegral.integral_mono_on (μ := volume) hv h₁ h₂
    (fun t ht => mul_le_mul_of_nonneg_left (hbound t ht.1) (sub_nonneg.mpr ht.2))
  have he : (∫ t in (0 : ℝ)..v, (v-t)*(M*(t^d/(d.factorial : ℝ)))) =
      M*lift (fun t : ℝ => t^d/(d.factorial : ℝ)) v := by
    unfold lift
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    ring
  rw [he, lift_factorial d hv] at hcmp
  exact hcmp

private theorem volterra_bound {f : ℝ → ℝ} (hf : Continuous f) (d : ℕ) (M : ℝ)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ f t)
    (hbound : ∀ t : ℝ, 0 ≤ t → f t ≤ M*(t^d/(d.factorial : ℝ)))
    {v : ℝ} (hv : 0 ≤ v) :
    volterra f v ≤ (M/3)*(v^(d+3)/((d+3).factorial : ℝ)) := by
  have hi : 0 ≤ ∫ s in (0 : ℝ)..v, coefficient s*lift f s :=
    intervalIntegral.integral_nonneg hv (fun s hs =>
      mul_nonneg (PrimePrefixCurvatureVolterraRecursion.result.2.2.1 s hs.1).1.le
        (lift_nonnegative hpos hs.1))
  have h₁ : IntervalIntegrable (fun s : ℝ => coefficient s*lift f s) volume 0 v :=
    (PrimePrefixCurvatureVolterraRecursion.result.1.mul (continuous_lift hf)).intervalIntegrable 0 v
  have h₂ : IntervalIntegrable (fun s : ℝ => (M/3)*(s^(d+2)/((d+2).factorial : ℝ))) volume 0 v :=
    (show Continuous (fun s : ℝ => (M/3)*(s^(d+2)/((d+2).factorial : ℝ))) by fun_prop).intervalIntegrable 0 v
  have hcmp := intervalIntegral.integral_mono_on (μ := volume) hv h₁ h₂ (fun s hs => by
    calc
      coefficient s*lift f s ≤ (1/3)*lift f s := mul_le_mul_of_nonneg_right
        (PrimePrefixCurvatureVolterraRecursion.result.2.2.1 s hs.1).2 (lift_nonnegative hpos hs.1)
      _ ≤ (1/3)*(M*(s^(d+2)/((d+2).factorial : ℝ))) :=
        mul_le_mul_of_nonneg_left (lift_bound hf d M hbound hs.1) (by norm_num)
      _ = (M/3)*(s^(d+2)/((d+2).factorial : ℝ)) := by ring)
  rw [intervalIntegral.integral_const_mul, integral_factorial (d+2) hv] at hcmp
  have hexp : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  unfold volterra
  calc
    Real.exp (-v)*(∫ s in (0 : ℝ)..v, coefficient s*lift f s) ≤
      1*(∫ s in (0 : ℝ)..v, coefficient s*lift f s) := mul_le_mul_of_nonneg_right hexp hi
    _ ≤ (M/3)*(v^(d+3)/((d+3).factorial : ℝ)) := by simpa [one_mul, Nat.add_assoc] using hcmp

private def majorant (n : ℕ) (v : ℝ) : ℝ :=
  (1/(2*3^n))*(v^(3*n)/((3*n).factorial : ℝ))

private theorem modelResidual_bound (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    modelResidual n v ≤ majorant n v := by
  induction n generalizing v with
  | zero =>
    change model v ≤ majorant 0 v
    rw [model_eq hv]
    simpa [majorant] using (curvature_bounds hv).2
  | succ n ih =>
    rw [modelResidual_step]
    have h := volterra_bound (continuous_modelResidual n) (3*n) (1/(2*3^n))
      (fun t ht => modelResidual_nonnegative n ht) (fun t ht => ih ht) hv
    have he : ((1/(2*3^n))/3)*(v^(3*n+3)/((3*n+3).factorial : ℝ)) =
        majorant (n+1) v := by
      have hn : 3*(n+1) = 3*n+3 := by omega
      rw [majorant, hn, pow_succ]
      field_simp
      ring
    exact h.trans_eq he

private theorem majorant_eq (n : ℕ) (v : ℝ) :
    majorant n v = v^(3*n)/(2*3^n*((3*n).factorial : ℝ)) := by
  unfold majorant
  ring

private theorem residual_bound (n : ℕ) {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ residual n v ∧ |residual n v| ≤
      v^(3*n)/(2*3^n*((3*n).factorial : ℝ)) := by
  have hpos : 0 ≤ residual n v := by rw [← modelResidual_eq n hv]; exact modelResidual_nonnegative n hv
  refine ⟨hpos, ?_⟩
  rw [abs_of_nonneg hpos, ← modelResidual_eq n hv, ← majorant_eq]
  exact modelResidual_bound n hv

private theorem compact_bound (n : ℕ) {V v : ℝ} (hv : v ∈ Icc 0 V) :
    |residual n v| ≤ V^(3*n)/(2*3^n*((3*n).factorial : ℝ)) := by
  exact (residual_bound n hv.1).2.trans
    (div_le_div_of_nonneg_right (pow_le_pow_left₀ hv.1 hv.2 _ ) (by positivity))

private theorem majorant_tendsto {V : ℝ} (hV : 0 ≤ V) :
    Tendsto (fun n : ℕ => V^(3*n)/(2*3^n*((3*n).factorial : ℝ))) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by positivity) (fun n => ?_)
    (FloorSemiring.tendsto_pow_div_factorial_atTop (V^3/3))
  have he : V^(3*n)/(2*3^n*((3*n).factorial : ℝ)) =
      (1/2)*((V^3/3)^n/((3*n).factorial : ℝ)) := by
    rw [div_pow, ← pow_mul]
    field_simp
  rw [he]
  have hp : 0 ≤ (V^3/3)^n := by positivity
  have hfac : (n.factorial : ℝ) ≤ ((3*n).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (show n ≤ 3*n by omega)
  calc
    (1/2)*((V^3/3)^n/((3*n).factorial : ℝ)) ≤
      (V^3/3)^n/((3*n).factorial : ℝ) := by nlinarith [div_nonneg hp (Nat.cast_nonneg ((3*n).factorial))]
    _ ≤ (V^3/3)^n/(n.factorial : ℝ) :=
      div_le_div_of_nonneg_left hp (by positivity) hfac

private theorem residual_uniform {V : ℝ} (hV : 0 ≤ V) :
    TendstoUniformlyOn residual (fun _ : ℝ => 0) atTop (Icc 0 V) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := (majorant_tendsto hV).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn
  intro v hv
  rw [Real.dist_eq, zero_sub, abs_neg]
  exact (compact_bound n hv).trans_lt hn

private theorem approximation_uniform {V : ℝ} (hV : 0 ≤ V) :
    TendstoUniformlyOn approximation curvature atTop (Icc 0 V) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have he := (majorant_tendsto hV).eventually (gt_mem_nhds hε)
  filter_upwards [he] with n hn
  intro v hv
  rw [Real.dist_eq]
  change |residual n v| < ε
  exact (compact_bound n hv).trans_lt hn

/-- Exact factorial errors and compact uniform recovery for the same actual recursion. -/
theorem result :
    (∀ (n : ℕ) (v : ℝ), 0 ≤ v →
      0 ≤ residual n v ∧ |residual n v| ≤
        v^(3*n)/(2*3^n*((3*n).factorial : ℝ))) ∧
    (∀ (V : ℝ), 0 ≤ V → ∀ (n : ℕ) (v : ℝ), v ∈ Icc 0 V →
      |residual n v| ≤ V^(3*n)/(2*3^n*((3*n).factorial : ℝ))) ∧
    (∀ (V : ℝ), 0 ≤ V →
      TendstoUniformlyOn residual (fun _ : ℝ => 0) atTop (Icc 0 V) ∧
      TendstoUniformlyOn approximation curvature atTop (Icc 0 V)) ∧
    (∀ (v : ℝ), 0 ≤ v →
      Tendsto (fun n : ℕ => residual n v) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => approximation n v) atTop (𝓝 (curvature v))) := by
  refine ⟨fun n v hv => residual_bound n hv,
    fun V _hV n v hv => compact_bound n hv,
    fun V hV => ⟨residual_uniform hV, approximation_uniform hV⟩, ?_⟩
  intro v hv
  exact ⟨(residual_uniform hv).tendsto_at ⟨hv, le_rfl⟩,
    (approximation_uniform hv).tendsto_at ⟨hv, le_rfl⟩⟩

end D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraFactorial

#print axioms D5.S3.Arith.Robin.PrimePrefixCurvatureVolterraFactorial.result
