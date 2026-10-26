/- GID: D5/S3/Geometry/Riemannian/QuadraticGradientFlow
   generality: G
   mirror-B: D5/B/S3/Geometry/Riemannian/QuadraticGradientFlow
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.InnerProductSpace.PiL2, mathlib/module/Mathlib.Analysis.Convex.Function, mathlib/module/Mathlib.Analysis.SpecialFunctions.ExpDeriv]
   utility: none
   digest: The anisotropic quadratic gradient flow is strictly longer than its chord at every positive horizon. -/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import D5.S3.Geometry.Riemannian.GradientDissipation
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Tactic

open Bundle Filter Manifold MeasureTheory Metric Set
open scoped Bundle Topology ContDiff ENNReal NNReal
open scoped InnerProductSpace
noncomputable section
namespace Original172.Example

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def point (u v : ℝ) : Plane := WithLp.toLp 2 ![u, v]
def potential (p : Plane) : ℝ := (p 0 ^ 2 + 2 * p 1 ^ 2) / 2
def flow (t : ℝ) : Plane := point (Real.exp (-t)) (Real.exp (-2*t))

theorem flow_hasDerivAt (t : ℝ) :
    HasDerivAt flow (point (-Real.exp (-t)) (-2*Real.exp (-2*t))) t := by
  set_option backward.isDefEq.respectTransparency false in
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa [Function.comp_def] using (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-2*s)) (-2*Real.exp (-2*t)) t := by
      simpa [Function.comp_def, mul_comm] using (Real.hasDerivAt_exp (-2*t)).comp t
        ((hasDerivAt_id t).const_mul (-2))
    convert (h1.smul_const (point 1 0)).add (h2.smul_const (point 0 1)) using 1
    · ext s i
      fin_cases i <;> simp [flow, point]
    · ext i
      fin_cases i <;> simp [point]

private theorem parabola_determinant (a : ℝ) :
    (a-1)*(a^4-a^2) - (a^2-1)*(a^2-a) = a*(a-1)^3*(a+1) := by
  ring

/-- A strict norm triangle, valid for every real 0<a<1. Its three vertices
are the actual points of the parabola, not a finite numerical test. -/
theorem parabola_strict_triangle {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ‖point (a^2) (a^4) - point 1 1‖ <
      ‖point a (a^2) - point 1 1‖ + ‖point (a^2) (a^4) - point a (a^2)‖ := by
  let u : Plane := point a (a^2) - point 1 1
  let v : Plane := point (a^2) (a^4) - point a (a^2)
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : Plane => z 0) h
    change a^2-a = 0 at h0
    nlinarith [mul_pos ha (sub_pos.mpr ha1)]
  have hdet : (a-1)*(a^4-a^2) - (a^2-1)*(a^2-a) ≠ 0 := by
    rw [parabola_determinant]
    exact mul_ne_zero (mul_ne_zero ha.ne' (pow_ne_zero 3 (sub_ne_zero.mpr ha1.ne)))
      (by linarith)
  have hne : ‖u+v‖ ≠ ‖u‖+‖v‖ := by
    intro h
    have hc := norm_add_eq_iff_real.mp h
    have h0 := congrArg (fun z : Plane => z 0) hc
    have h1 := congrArg (fun z : Plane => z 1) hc
    change ‖v‖*(a-1) = ‖u‖*(a^2-a) at h0
    change ‖v‖*(a^2-1) = ‖u‖*(a^4-a^2) at h1
    have hz : ‖v‖*((a-1)*(a^4-a^2) - (a^2-1)*(a^2-a)) = 0 := by
      nlinarith [congrArg (fun r : ℝ => r*(a^4-a^2)) h0,
        congrArg (fun r : ℝ => r*(a^2-a)) h1]
    exact (mul_ne_zero (norm_ne_zero_iff.mpr hv) hdet) hz
  have hlt := lt_of_le_of_ne (norm_add_le u v) hne
  have huv : u+v = point (a^2) (a^4) - point 1 1 := by dsimp [u,v]; abel
  simpa only [huv] using hlt


local notation "IP" => 𝓘(ℝ,Plane)
local notation "IR" => 𝓘(ℝ,ℝ)

private def potentialDifferential (p : Plane) : Plane →L[ℝ] ℝ :=
  (p 0) • EuclideanSpace.proj 0 + (2*p 1) • EuclideanSpace.proj 1

private theorem potential_hasFDerivAt (p : Plane) :
    HasFDerivAt potential (potentialDifferential p) p := by
  have h0 := (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 0).hasFDerivAt (x:=p)
  have h1 := (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).hasFDerivAt (x:=p)
  convert ((h0.pow 2).add ((h1.pow 2).const_mul 2)).const_mul (1/2:ℝ) using 1
  · funext q
    dsimp [potential]
    ring
  · ext w
    simp [potentialDifferential]
    <;> ring

private theorem potential_gradient (p : Plane) :
    actualGradient potential p = point (p 0) (2*p 1) := by
  set_option backward.isDefEq.respectTransparency false in
    apply (InnerProductSpace.toDual ℝ (TangentSpace IP p)).injective
    rw [actualGradient, LinearIsometryEquiv.apply_symm_apply]
    ext w
    rw [mfderiv_eq_fderiv, (potential_hasFDerivAt p).fderiv]
    change (p 0)*((show Plane from w) 0)+(2*p 1)*((show Plane from w) 1) =
      inner ℝ (point (p 0) (2*p 1)) (show Plane from w)
    simp [PiLp.inner_apply, Fin.sum_univ_two, point, Real.inner_apply]
    <;> ring

private theorem potential_C1 : ContMDiff IP IR 1 potential := by
  rw [contMDiff_iff_contDiff]
  have h0 : ContDiff ℝ 1 (fun q : Plane => q 0) :=
    (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 0).contDiff
  have h1 : ContDiff ℝ 1 (fun q : Plane => q 1) :=
    (EuclideanSpace.proj (𝕜:=ℝ) (ι:=Fin 2) 1).contDiff
  exact ((h0.pow 2).add (contDiff_const.mul (h1.pow 2))).div_const 2

private theorem flow_basis (t : ℝ) : flow t =
    Real.exp (-t) • point 1 0 + Real.exp (-2*t) • point 0 1 := by
  ext i
  fin_cases i <;> simp [flow, point, WithLp.ofLp_neg] <;> rfl

private theorem flow_C1 : ContMDiff IR IP 1 flow := by
  rw [contMDiff_iff_contDiff]
  have heq : flow = fun t : ℝ =>
      Real.exp (-t) • point 1 0 + Real.exp (-2*t) • point 0 1 :=
    funext flow_basis
  rw [heq]
  fun_prop

private theorem flow_gradient_equation (t : ℝ) :
    mfderiv IR IP flow t 1 = -actualGradient potential (flow t) := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ flow t 1 = -actualGradient potential (flow t)
  rw [fderiv_apply_one_eq_deriv, (flow_hasDerivAt t).deriv, potential_gradient]
  ext i
  fin_cases i <;> simp [flow, point, WithLp.ofLp_neg] <;> rfl

/-- Both exponential identities are proved for arbitrary T, before any norm
or length comparison is made. -/
private theorem flow_midpoint_values (T : ℝ) :
    flow 0 = point 1 1 ∧
    flow (T/2) = point (Real.exp (-T/2)) ((Real.exp (-T/2))^2) ∧
    flow T = point ((Real.exp (-T/2))^2) ((Real.exp (-T/2))^4) := by
  have h2 : Real.exp (-T) = Real.exp (-T/2)^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have h4 : Real.exp (-2*T) = Real.exp (-T/2)^4 := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨by simp [flow], ?_, ?_⟩
  · dsimp [flow]
    rw [show -2*(T/2) = -T by ring, h2]
    congr 1 <;> congr 1 <;> ring
  · simp only [flow, h2, h4]

private theorem plane_intrinsic_real (p q : Plane) :
    (riemannianEDist IP p q).toReal = ‖q-p‖ := by
  rw [← (IsRiemannianManifold.out (I := IP)), edist_dist, ENNReal.toReal_ofReal dist_nonneg,
    dist_eq_norm, norm_sub_rev]

theorem S8_actual_strict_length_and_nonattainment {T : ℝ} (hT : 0 < T) :
    pathELength IP flow 0 T < ⊤ ∧
    (riemannianEDist IP (flow 0) (flow T)).toReal <
      (pathELength IP flow 0 T).toReal ∧
    (riemannianEDist IP (flow 0) (flow T))^2 /
      ((2:ℝ≥0∞)*ENNReal.ofReal T) < kineticAction (E := Plane) flow T := by
  letI : IsContinuousRiemannianBundle Plane
      (TangentSpace IP : Plane → Type _) := by
    refine ⟨(riemannianMetricVectorSpace Plane).inner, ?_, ?_⟩
    · exact (riemannianMetricVectorSpace Plane).contMDiff.continuous
    · intro p v w
      rfl
  have hx : ContMDiffOn IR IP 1 flow (Icc (0:ℝ) T) := flow_C1.contMDiffOn
  have hAC := S1_C1_to_actual_metric_AC hT flow hx
  have hflow : ∀ t ∈ Icc (0:ℝ) T,
      mfderivWithin IR IP flow (Icc (0:ℝ) T) t 1 =
        -actualGradient potential (flow t) := by
    intro t ht
    rw [mfderivWithin_eq_mfderiv
      ((uniqueDiffOn_Icc hT).uniqueMDiffOn t ht)
      (flow_C1.mdifferentiable (by norm_num) t)]
    exact flow_gradient_equation t
  obtain ⟨_, hi2, hdrop⟩ := S2_dissipation hT potential flow potential_C1 hx hflow
  obtain ⟨hL, hLi, hA, hAi, hsq⟩ := actual_length_energy_real hT flow hAC hi2
  obtain ⟨_, _, hi, _, _, _, _, _, hchord⟩ :=
    actual_AC_speed_variation_length hT flow hAC
  have hchordNorm : ∀ a ∈ Icc (0:ℝ) T, ∀ b ∈ Icc (0:ℝ) T, a ≤ b →
      ‖flow b - flow a‖ ≤ ∫ t in a..b, ‖mfderiv IR IP flow t 1‖ := by
    intro a ha b hb hab
    have hd := hchord a ha b hb hab
    change (riemannianEDist IP (flow a) (flow b)).toReal ≤ _ at hd
    simpa only [plane_intrinsic_real] using hd
  have hm : T/2 ∈ Icc (0:ℝ) T := ⟨by linarith, by linarith⟩
  have h0 : (0:ℝ) ∈ Icc (0:ℝ) T := ⟨le_rfl,hT.le⟩
  have h1 : T ∈ Icc (0:ℝ) T := ⟨hT.le,le_rfl⟩
  have hseg0 := hchordNorm 0 h0 (T/2) hm hm.1
  have hseg1 := hchordNorm (T/2) hm T h1 hm.2
  have hi0 : IntervalIntegrable (fun t => ‖mfderiv IR IP flow t 1‖) volume 0 (T/2) := by
    apply hi.mono_set
    rw [uIcc_of_le hm.1, uIcc_of_le hT.le]
    exact Icc_subset_Icc le_rfl hm.2
  have hi1 : IntervalIntegrable (fun t => ‖mfderiv IR IP flow t 1‖) volume (T/2) T := by
    apply hi.mono_set
    rw [uIcc_of_le hm.2, uIcc_of_le hT.le]
    exact Icc_subset_Icc hm.1 le_rfl
  let a := Real.exp (-T/2)
  have ha : 0 < a := Real.exp_pos _
  have ha1 : a < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  obtain ⟨hx0, hxm, hxT⟩ := flow_midpoint_values T
  have htriangle : ‖flow T - flow 0‖ <
      ‖flow (T/2) - flow 0‖ + ‖flow T - flow (T/2)‖ := by
    rw [hx0, hxm, hxT]
    exact parabola_strict_triangle ha ha1
  have hstrict : (riemannianEDist IP (flow 0) (flow T)).toReal <
      (pathELength IP flow 0 T).toReal := by
    rw [plane_intrinsic_real, hLi]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi0 hi1
    exact htriangle.trans_le ((add_le_add hseg0 hseg1).trans_eq hsplit)
  refine ⟨hL, hstrict, ?_⟩
  have hlength_drop : (pathELength IP flow 0 T).toReal^2 ≤
      T * (potential (flow 0) - potential (flow T)) := by
    rw [hdrop]
    exact hsq
  have haction_drop : (kineticAction (E := Plane) flow T).toReal =
      (potential (flow 0) - potential (flow T))/2 := by
    rw [hdrop]
    exact hAi
  have hdfin : riemannianEDist IP (flow 0) (flow T) ≠ ⊤ := by
    rw [← (IsRiemannianManifold.out (I := IP))]
    exact edist_ne_top _ _
  have hτ0 : ENNReal.ofReal T ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hT)
  have hden0 : (2:ℝ≥0∞)*ENNReal.ofReal T ≠ 0 :=
    mul_ne_zero (by norm_num) hτ0
  have hleft : (riemannianEDist IP (flow 0) (flow T))^2 /
      ((2:ℝ≥0∞)*ENNReal.ofReal T) ≠ ⊤ := by
    finiteness
  have hsqstrict : (riemannianEDist IP (flow 0) (flow T)).toReal^2 <
      T * (potential (flow 0) - potential (flow T)) := by
    have hsum : 0 < (pathELength IP flow 0 T).toReal +
        (riemannianEDist IP (flow 0) (flow T)).toReal := by
      have := ENNReal.toReal_nonneg (a:=riemannianEDist IP (flow 0) (flow T))
      linarith
    have hp := mul_pos (sub_pos.mpr hstrict) hsum
    nlinarith
  apply (ENNReal.toReal_lt_toReal hleft hA.ne).mp
  rw [haction_drop, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hT.le]
  norm_num
  apply (div_lt_iff₀ (by positivity : 0 < (2:ℝ)*T)).mpr
  nlinarith


end Original172.Example
