/- GID: D5/S3/Geometry/Hyperideal/ActualRaysJointAngle
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/ActualRaysJointAngle
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [mathlib/module/Mathlib.Analysis.Calculus.DSlope]
   utility: none
   digest: Global Lorentz rays in the original hyperbolic metric and the unrestricted joint comparison-angle limit. -/

import D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

noncomputable section
open scoped BigOperators Topology
open Set Filter
open D5.S3.Geometry.Hyperideal.LengthGramBody
open D5.S3.Geometry.HyperbolicUpperHalfSpace
open D5.S3.Geometry.Hyperideal.LengthGramMetricSegments
namespace D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem tangent_time_bound (Y U : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hU : lorentz U U = 1) (ho : lorentz Y U = 0) : |U 3| < Y 3 := by
  simp [lorentz, Fin.sum_univ_succ] at hY hU ho
  have hy : Y 0^2 + Y 1^2 + Y 2^2 = Y 3^2 - 1 := by nlinarith
  have hu : U 0^2 + U 1^2 + U 2^2 = U 3^2 + 1 := by nlinarith
  have hb : Y 0*U 0 + Y 1*U 1 + Y 2*U 2 = Y 3*U 3 := by linarith
  have hcs : (Y 0*U 0 + Y 1*U 1 + Y 2*U 2)^2 ≤
      (Y 0^2 + Y 1^2 + Y 2^2) * (U 0^2 + U 1^2 + U 2^2) := by
    simpa [Fin.sum_univ_succ, add_assoc] using
      (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun i : Fin 3 => Y i.castSucc) (fun i : Fin 3 => U i.castSucc))
  rw [hy, hu, hb] at hcs
  nlinarith [sq_abs (U 3), abs_nonneg (U 3)]

private theorem ray_future (Y U : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hU : lorentz U U = 1) (ho : lorentz Y U = 0) (t : ℝ) :
    0 < (Real.cosh t • Y + Real.sinh t • U) 3 := by
  have hb := tangent_time_bound Y U hY ht hU ho
  have hc := Real.cosh_pos t
  have hs : |Real.sinh t| < Real.cosh t := by
    nlinarith [Real.cosh_sq_sub_sinh_sq t, sq_abs (Real.sinh t), abs_nonneg (Real.sinh t)]
  have hp := mul_pos hc (sub_pos.mpr hb)
  have hle := mul_le_mul_of_nonneg_right hs.le (abs_nonneg (U 3))
  have ha := neg_abs_le (Real.sinh t * U 3)
  rw [abs_mul] at ha
  change 0 < Real.cosh t * Y 3 + Real.sinh t * U 3
  nlinarith

private theorem ray_pair (Y U V : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (hU : lorentz Y U = 0)
    (hV : lorentz Y V = 0) (s t : ℝ) :
    lorentz (Real.cosh s • Y + Real.sinh s • U)
      (Real.cosh t • Y + Real.sinh t • V) =
      -(Real.cosh s * Real.cosh t - lorentz U V * Real.sinh s * Real.sinh t) := by
  rw [lorentz_linear, lorentz_symm U Y, hY, hU, hV]
  ring

private theorem actual_line (Y U : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hU : lorentz U U = 1) (ho : lorentz Y U = 0) :
    ∃ gamma : ℝ → HyperbolicThreeSpace,
      Isometry gamma ∧ gamma 0 = project Y hY ht ∧
      ∀ t, lift (gamma t) = Real.cosh t • Y + Real.sinh t • U := by
  let W := fun t : ℝ => Real.cosh t • Y + Real.sinh t • U
  have hu (t : ℝ) : lorentz (W t) (W t) = -1 := by
    have h := ray_pair Y U U hY ho ho t t
    rw [hU] at h
    dsimp [W]
    nlinarith [Real.cosh_sq_sub_sinh_sq t]
  have hf (t : ℝ) : 0 < W t 3 := ray_future Y U hY ht hU ho t
  let gamma := fun t => project (W t) (hu t) (hf t)
  have hl (t : ℝ) : lift (gamma t) = W t :=
    lift_of_coordinates _ _ (hu t) (hf t) rfl
  refine ⟨gamma, ?_, ?_, hl⟩
  · apply Isometry.of_dist_eq
    intro s t
    apply Real.cosh_strictMonoOn.injOn dist_nonneg dist_nonneg
    have hp := ray_pair Y U U hY ho ho s t
    rw [hU] at hp
    change lorentz (W s) (W t) = _ at hp
    rw [← hl s, ← hl t, lift_cosh] at hp
    simpa [Real.dist_eq, Real.cosh_abs, Real.cosh_sub] using neg_injective hp
  · apply lift_injective
    rw [hl, lift_of_coordinates _ _ hY ht rfl]
    simp [W]

private def sinhc (x : ℝ) : ℝ := dslope Real.sinh 0 x

private theorem sinhc_zero : sinhc 0 = 1 := by
  simp [sinhc, Real.deriv_sinh]

private theorem mul_sinhc (x : ℝ) : x * sinhc x = Real.sinh x := by
  simpa [sinhc] using sub_smul_dslope Real.sinh 0 x

private theorem sinhc_continuous : ContinuousAt sinhc 0 :=
  continuousAt_dslope_same.mpr (Real.differentiableAt_sinh)

private theorem sinhc_pos (x : ℝ) (hx : 0 ≤ x) : 0 < sinhc x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h, sinhc_zero]; norm_num
  · have hs := Real.sinh_pos_iff.mpr h
    have hm := mul_sinhc x
    exact pos_of_mul_pos_right (hm.symm ▸ hs) h.le

private theorem cosine_extension (s t d c : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hd : |s-t| ≤ d)
    (hlaw : Real.cosh d = Real.cosh s * Real.cosh t - c * Real.sinh s * Real.sinh t) :
    (s^2+t^2-d^2)/(2*s*t) =
      1 - (1-c)*sinhc s*sinhc t /
        (sinhc ((d+|s-t|)/2)*sinhc ((d-|s-t|)/2)) := by
  let a := (d+|s-t|)/2
  let e := (d-|s-t|)/2
  have ha : 0 ≤ a := by dsimp [a]; linarith [abs_nonneg (s-t)]
  have he : 0 ≤ e := by dsimp [e]; linarith
  have hden : sinhc a * sinhc e ≠ 0 := (mul_pos (sinhc_pos a ha) (sinhc_pos e he)).ne'
  have hsum : a+e = d := by dsimp [a,e]; ring
  have hsub : a-e = |s-t| := by dsimp [a,e]; ring
  have hh : 2 * Real.sinh a * Real.sinh e =
      (1-c)*Real.sinh s*Real.sinh t := by
    have h1 := Real.cosh_add a e
    have h2 := Real.cosh_sub a e
    rw [hsum] at h1
    rw [hsub, Real.cosh_abs, Real.cosh_sub] at h2
    rw [hlaw] at h1
    nlinarith
  rw [← mul_sinhc a, ← mul_sinhc e, ← mul_sinhc s, ← mul_sinhc t] at hh
  have hae : 4*a*e = d^2-(s-t)^2 := by
    dsimp [a,e]
    nlinarith [sq_abs (s-t)]
  change _ = 1 - (1-c)*sinhc s*sinhc t / (sinhc a*sinhc e)
  field_simp [hden, (sinhc_pos a ha).ne', (sinhc_pos e he).ne', hs.ne', ht.ne']
  nlinarith only [hh, congrArg (fun x : ℝ => x * (sinhc a * sinhc e)) hae]

private theorem joint_angle_limit (D : ℝ × ℝ → ℝ) (c : ℝ)
    (hD : Continuous D) (h0 : D (0,0) = 0)
    (hb : ∀ s t, 0 < s → 0 < t → |s-t| ≤ D (s,t))
    (hlaw : ∀ s t, Real.cosh (D (s,t)) =
      Real.cosh s * Real.cosh t - c * Real.sinh s * Real.sinh t) :
    Tendsto (fun z : ℝ × ℝ => Real.arccos
      ((z.1^2+z.2^2-D z^2)/(2*z.1*z.2)))
      (𝓝[Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)] ((0:ℝ),(0:ℝ))) (𝓝 (Real.arccos c)) := by
  let A := fun z : ℝ × ℝ => (D z+|z.1-z.2|)/2
  let E := fun z : ℝ × ℝ => (D z-|z.1-z.2|)/2
  let F := fun z : ℝ × ℝ => 1 - (1-c)*sinhc z.1*sinhc z.2/(sinhc (A z)*sinhc (E z))
  have hA : Continuous A := (hD.add ((continuous_fst.sub continuous_snd).abs)).div_const 2
  have hE : Continuous E := (hD.sub ((continuous_fst.sub continuous_snd).abs)).div_const 2
  have hA0 : A (0,0) = 0 := by simp [A,h0]
  have hE0 : E (0,0) = 0 := by simp [E,h0]
  have hcA : ContinuousAt (fun z => sinhc (A z)) (0,0) :=
    sinhc_continuous.comp_of_eq hA.continuousAt hA0
  have hcE : ContinuousAt (fun z => sinhc (E z)) (0,0) :=
    sinhc_continuous.comp_of_eq hE.continuousAt hE0
  have hcf : ContinuousAt F (0,0) := by
    have hfst : ContinuousAt (fun z : ℝ × ℝ => sinhc z.1) ((0,0) : ℝ × ℝ) := by
      apply sinhc_continuous.comp_of_eq
      · exact continuous_fst.continuousAt
      · rfl
    have hsnd : ContinuousAt (fun z : ℝ × ℝ => sinhc z.2) ((0,0) : ℝ × ℝ) := by
      apply sinhc_continuous.comp_of_eq
      · exact continuous_snd.continuousAt
      · rfl
    apply continuousAt_const.sub
    apply ContinuousAt.div
    · exact ((continuousAt_const.mul hfst).mul hsnd)
    · exact hcA.mul hcE
    · simp [hA0,hE0,sinhc_zero]
  have hf0 : F (0,0) = c := by simp [F,hA0,hE0,sinhc_zero]
  have ht : Tendsto F (𝓝[Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)] ((0:ℝ),(0:ℝ))) (𝓝 c) := by
    rw [← hf0]
    exact hcf.tendsto.mono_left nhdsWithin_le_nhds
  refine Filter.Tendsto.congr' ?_ ht.arccos
  filter_upwards [self_mem_nhdsWithin] with z hz
  congr 1
  exact (cosine_extension z.1 z.2 (D z) c hz.1 hz.2 (hb _ _ hz.1 hz.2) (hlaw _ _)).symm

/-- Actual global unit-speed lines through any future unit Lorentz point, with the
full joint positive-quadrant comparison-angle limit, including coincident rays. -/
theorem actual_rays_joint_angle (Y U V : Fin 4 → ℝ)
    (hY : lorentz Y Y = -1) (ht : 0 < Y 3)
    (hU : lorentz U U = 1) (hV : lorentz V V = 1)
    (hYU : lorentz Y U = 0) (hYV : lorentz Y V = 0)
    (hc : lorentz U V ∈ Icc (-1:ℝ) 1) :
    ∃ gammaU gammaV : ℝ → HyperbolicThreeSpace,
      Isometry gammaU ∧ Isometry gammaV ∧
      gammaU 0 = project Y hY ht ∧ gammaV 0 = project Y hY ht ∧
      (∀ t, lift (gammaU t) = Real.cosh t • Y + Real.sinh t • U) ∧
      (∀ t, lift (gammaV t) = Real.cosh t • Y + Real.sinh t • V) ∧
      (∀ s t, Real.cosh (dist (gammaU s) (gammaV t)) =
        Real.cosh s * Real.cosh t - lorentz U V * Real.sinh s * Real.sinh t) ∧
      (∀ s t, 0 ≤ s → 0 ≤ t →
        |s-t| ≤ dist (gammaU s) (gammaV t) ∧ dist (gammaU s) (gammaV t) ≤ s+t) ∧
      Tendsto (fun z : ℝ × ℝ => Real.arccos
        ((z.1^2+z.2^2-dist (gammaU z.1) (gammaV z.2)^2)/(2*z.1*z.2)))
        (𝓝[Set.Ioi (0:ℝ) ×ˢ Set.Ioi (0:ℝ)] ((0:ℝ),(0:ℝ)))
        (𝓝 (Real.arccos (lorentz U V))) := by
  obtain ⟨gu,hiu,h0u,hlu⟩ := actual_line Y U hY ht hU hYU
  obtain ⟨gv,hiv,h0v,hlv⟩ := actual_line Y V hY ht hV hYV
  have hbase : gu 0 = gv 0 := h0u.trans h0v.symm
  have hlaw (s t : ℝ) : Real.cosh (dist (gu s) (gv t)) =
      Real.cosh s * Real.cosh t - lorentz U V * Real.sinh s * Real.sinh t := by
    have h := ray_pair Y U V hY hYU hYV s t
    rw [← hlu s, ← hlv t, lift_cosh] at h
    exact neg_injective h
  have hb (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
      |s-t| ≤ dist (gu s) (gv t) ∧ dist (gu s) (gv t) ≤ s+t := by
    have hu : dist (gu s) (gu 0) = s := by rw [hiu.dist_eq]; simp [Real.dist_eq, abs_of_nonneg hs]
    have hv : dist (gv t) (gu 0) = t := by rw [hbase,hiv.dist_eq]; simp [Real.dist_eq, abs_of_nonneg ht]
    constructor
    · simpa [hu,hv] using abs_dist_sub_le (gu s) (gv t) (gu 0)
    · have h := dist_triangle (gu s) (gu 0) (gv t)
      rw [hu, dist_comm (gu 0), hv] at h
      exact h
  refine ⟨gu,gv,hiu,hiv,h0u,h0v,hlu,hlv,hlaw,hb,?_⟩
  apply joint_angle_limit (fun z : ℝ × ℝ => dist (gu z.1) (gv z.2)) (lorentz U V)
  · exact (hiu.continuous.comp continuous_fst).dist (hiv.continuous.comp continuous_snd)
  · simp [hbase]
  · intro s t hs ht; exact (hb s t hs.le ht.le).1
  · exact hlaw

#print axioms actual_rays_joint_angle
end D5.S3.Geometry.Hyperideal.ActualRaysJointAngle
