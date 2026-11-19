/- GID: D5/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/TwistedGround/Signed/SpatialUniqueness
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Homogeneous spatial uniqueness in the six negative-label J/T sectors. -/

import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianExternalGeneratedSource
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
open OriginalGaussianExternalGeneratedSource

private def sigma (square : Bool) : ℂ := if square then -1 else 1

private def beta (e : Bool) (w : ℂ) : ℂ :=
  if e then (1 - 3 * w) / 2 else -(1 + w) / 2

private def spatial (e f square : Bool) (F : ℂ × ℂ → ℂ) (u v : ℂ) : ℂ :=
  modeScale f v *
      (u * (1 - u) * deriv (fun w => F (w, v)) u + beta e u * F (u, v)) +
    sigma square * modeScale e u *
      (v * (1 - v) * deriv (fun w => F (u, w)) v + beta f v * F (u, v))

-- A single radius works for every complex u in its open ball and every t∈[0,1].
private def radius (R : ℝ) (f : Bool) (v : ℂ) : ℝ :=
  if f then (R - ‖v‖) / 8 else min ((R - ‖v‖) / 8) (‖v‖ / 8)

private def pathDen (f square : Bool) (u v z : ℂ) : ℂ :=
  if f then
    if square then 1 - u * (1 - v + z * v)
    else 1 - u * (z + (1 - z) * v)
  else if square then 1 - z * u else 1 - u

private def pathY (f square : Bool) (u v z : ℂ) : ℂ :=
  if f then
    if square then v * (1 - z * u) / pathDen f square u v z
    else v * (1 - u) / pathDen f square u v z
  else if square then 1 - (1 - v) * (1 - u) / pathDen f square u v z
    else 1 - (1 - v) * (1 - z * u) / pathDen f square u v z

private def velocity (f square : Bool) (u x y : ℂ) : ℂ :=
  sigma square * u * (if f then y else 1) * (1 - y) / (1 - x)

-- This is c, rather than a=c/2: the path equation is 2 z h' = c h.
private def coefficient (f square : Bool) (x y : ℂ) : ℂ :=
  (1 + x - 2 * sigma square * x * beta f y / modeScale f y) / (1 - x)

private def gaugeCore (f square : Bool) (x y : ℂ) : ℂ :=
  if f then
    if square then (1 - x) ^ 3 * (1 - y) ^ 3 else (1 - x) * (1 - y) ^ 3
  else if square then 1 / y else (1 - x) ^ 4 / y

private def gaugePrime (f square : Bool) (u x y dy : ℂ) : ℂ :=
  if f then
    if square then
      -3 * u * (1 - x) ^ 2 * (1 - y) ^ 3 -
        3 * (1 - x) ^ 3 * (1 - y) ^ 2 * dy
    else -u * (1 - y) ^ 3 - 3 * (1 - x) * (1 - y) ^ 2 * dy
  else if square then -dy / y ^ 2
    else (-4 * u * (1 - x) ^ 3 * y - (1 - x) ^ 4 * dy) / y ^ 2

private def pathGauge (f square : Bool) (u v z : ℂ) : ℂ :=
  gaugeCore f square (z * u) (pathY f square u v z)

private lemma radius_pos {R : ℝ} {f : Bool} {v : ℂ}
    (hv : ‖v‖ < R) (hv0 : f = false → v ≠ 0) : 0 < radius R f v := by
  cases f
  · simp only [radius, Bool.false_eq_true, ite_false]
    exact lt_min (by linarith) (div_pos (norm_pos_iff.mpr (hv0 rfl)) (by norm_num))
  · simpa only [radius, ite_true] using (show 0 < (R - ‖v‖) / 8 by linarith)

private lemma radius_bounds {R : ℝ} {f : Bool} {u v : ℂ}
    (hR : R ≤ 1) (hu : ‖u‖ < radius R f v) :
    ‖u‖ < R ∧ ‖u‖ < 1 / 8 ∧ 8 * ‖u‖ < R - ‖v‖ ∧
      (f = false → 8 * ‖u‖ < ‖v‖) := by
  have ha : ‖u‖ < (R - ‖v‖) / 8 := by
    cases f
    · exact hu.trans_le (min_le_left _ _)
    · exact hu
  have hb : f = false → ‖u‖ < ‖v‖ / 8 := by
    intro hf
    subst f
    exact hu.trans_le (min_le_right _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · linarith [norm_nonneg u, norm_nonneg v]
  · linarith [norm_nonneg v]
  · linarith
  · intro hf
    have := hb hf
    linarith

private lemma one_sub_ne_zero {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have he : w = 1 := (sub_eq_zero.mp h).symm
  simpa [he] using hw

private lemma real_parameter_bounds {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(t : ℂ)‖ ≤ 1 ∧ ‖1 - (t : ℂ)‖ ≤ 1 := by
  constructor
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
  · have he : (1 : ℂ) - (t : ℂ) = ((1 - t : ℝ) : ℂ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.2] : 0 ≤ 1 - t)]
    linarith [ht.1]

private lemma denominator_lower_bound {f square : Bool} {u v : ℂ} {t : ℝ}
    (hu : ‖u‖ < 1 / 8) (hv : ‖v‖ < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 / 2 : ℝ) < ‖pathDen f square u v (t : ℂ)‖ := by
  have htN := (real_parameter_bounds ht).1
  have h1tN := (real_parameter_bounds ht).2
  have hprod' : ‖(1 - (t : ℂ)) * v‖ ≤ ‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg v) h1tN
  have hp : ‖(t : ℂ) + (1 - (t : ℂ)) * v‖ ≤ 2 := by
    have := norm_add_le (t : ℂ) ((1 - (t : ℂ)) * v)
    linarith
  have hm : ‖1 - v + (t : ℂ) * v‖ ≤ 2 := by
    have he : (1 : ℂ) - v + (t : ℂ) * v = 1 - (1 - (t : ℂ)) * v := by ring
    rw [he]
    have := norm_sub_le (1 : ℂ) ((1 - (t : ℂ)) * v)
    norm_num only [norm_one] at this
    linarith
  have hsmall (w : ℂ) (hw : ‖w‖ ≤ 2) : (1 / 2 : ℝ) < ‖1 - u * w‖ := by
    have hmul : ‖u * w‖ ≤ 2 * ‖u‖ := by
      rw [norm_mul]
      nlinarith [norm_nonneg u]
    have hlow := norm_sub_norm_le (1 : ℂ) (u * w)
    norm_num only [norm_one] at hlow
    linarith
  cases f <;> cases square
  · simpa only [pathDen, Bool.false_eq_true, ite_false, mul_one] using
      hsmall 1 (by norm_num)
  · have he : 1 - (t : ℂ) * u = 1 - u * (t : ℂ) := by ring
    simpa only [pathDen, Bool.false_eq_true, ite_false, ite_true, he] using
      hsmall (t : ℂ) (by linarith)
  · simpa only [pathDen, Bool.false_eq_true, ite_false, ite_true] using hsmall _ hp
  · simpa only [pathDen, ite_true] using hsmall _ hm

private lemma path_displacement (f square : Bool) (u v z : ℂ)
    (hd : pathDen f square u v z ≠ 0) :
    pathY f square u v z - v =
      (if square then (1 : ℂ) else -1) * u * (1 - z) * (1 - v) *
        (if f then v else 1) / pathDen f square u v z := by
  cases f <;> cases square <;>
    simp only [pathY, Bool.false_eq_true, ite_false, ite_true] <;>
    generalize hD : pathDen _ _ u v z = d at hd ⊢ <;>
    field_simp [hd] <;>
    rw [← hD] <;>
    simp only [pathDen, Bool.false_eq_true, ite_false, ite_true] <;> ring

private lemma path_displacement_bound {f square : Bool} {u v : ℂ} {t : ℝ}
    (hu : ‖u‖ < 1 / 8) (hv : ‖v‖ < 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖pathY f square u v (t : ℂ) - v‖ ≤ 4 * ‖u‖ := by
  have hd := denominator_lower_bound (f := f) (square := square) hu hv ht
  have hdn : pathDen f square u v (t : ℂ) ≠ 0 := norm_pos_iff.mp (by linarith)
  have ht1 := (real_parameter_bounds ht).2
  have hv1 : ‖1 - v‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) v
    norm_num only [norm_one] at this
    linarith
  have hfactor : ‖(if f then v else (1 : ℂ))‖ ≤ 1 := by
    cases f
    · simp
    · simpa only [ite_true] using hv.le
  have hsign : ‖(if square then (1 : ℂ) else -1)‖ = 1 := by cases square <;> norm_num
  rw [path_displacement f square u v (t : ℂ) hdn, norm_div,
    norm_mul, norm_mul, norm_mul, norm_mul, hsign, one_mul]
  apply (div_le_iff₀ (by linarith : 0 < ‖pathDen f square u v (t : ℂ)‖)).mpr
  calc
    ‖u‖ * ‖1 - (t : ℂ)‖ * ‖1 - v‖ * ‖(if f then v else (1 : ℂ))‖
        ≤ ‖u‖ * 1 * 2 * 1 := by gcongr <;> assumption
    _ ≤ 4 * ‖u‖ * ‖pathDen f square u v (t : ℂ)‖ := by
      nlinarith [norm_nonneg u]

private structure PathDomain (R : ℝ) (f square : Bool) (u v : ℂ) (t : ℝ) : Prop where
  x_mem : ‖(t : ℂ) * u‖ < R
  y_mem : ‖pathY f square u v (t : ℂ)‖ < R
  u_ne : 1 - u ≠ 0
  x_ne : 1 - (t : ℂ) * u ≠ 0
  den_ne : pathDen f square u v (t : ℂ) ≠ 0
  y_ne_one : 1 - pathY f square u v (t : ℂ) ≠ 0
  scale_ne : modeScale f (pathY f square u v (t : ℂ)) ≠ 0

private lemma path_domain {R : ℝ} {f square : Bool} {u v : ℂ} {t : ℝ}
    (hR : R ≤ 1) (hv : ‖v‖ < R) (hu : ‖u‖ < radius R f v)
    (ht : t ∈ Icc (0 : ℝ) 1) : PathDomain R f square u v t := by
  have hb := radius_bounds hR hu
  have hxN : ‖(t : ℂ) * u‖ ≤ ‖u‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg u) (real_parameter_bounds ht).1
  have hxR : ‖(t : ℂ) * u‖ < R := hxN.trans_lt hb.1
  have hdisp := path_displacement_bound (f := f) (square := square) hb.2.1 (hv.trans_le hR) ht
  have hyR : ‖pathY f square u v (t : ℂ)‖ < R := by
    have htri := norm_add_le (pathY f square u v (t : ℂ) - v) v
    rw [sub_add_cancel] at htri
    linarith [norm_nonneg u]
  refine ⟨hxR, hyR, one_sub_ne_zero (by linarith [hb.2.1]),
    one_sub_ne_zero (hxR.trans_le hR), ?_, one_sub_ne_zero (hyR.trans_le hR), ?_⟩
  · exact norm_pos_iff.mp (lt_trans (by norm_num)
      (denominator_lower_bound hb.2.1 (hv.trans_le hR) ht))
  · cases f
    · change pathY false square u v (t : ℂ) ≠ 0
      intro hz
      have hvm := hb.2.2.2 rfl
      rw [hz, zero_sub, norm_neg] at hdisp
      linarith [norm_nonneg u]
    · simp [modeScale]

private lemma pathY_one (f square : Bool) (u v : ℂ) (hu : 1 - u ≠ 0) :
    pathY f square u v 1 = v := by
  cases f <;> cases square <;>
    simp only [pathY, pathDen, Bool.false_eq_true, ite_false, ite_true,
      one_mul, sub_self, zero_mul, add_zero, sub_add_cancel] <;>
    field_simp [hu] <;> ring

-- The same coordinate-inclusion / linear-map calculation used by the pinned
-- positive-J path proof; the two scalar derivatives are the literal PDE ones.
private lemma coordinate_chain {F : ℂ × ℂ → ℂ} {L : (ℂ × ℂ) →L[ℂ] ℂ}
    {x y : ℂ → ℂ} {z dx dy : ℂ}
    (hF : HasFDerivAt F L (x z, y z))
    (hx : HasDerivAt x dx z) (hy : HasDerivAt y dy z) :
    HasDerivAt (fun w => F (x w, y w))
      (dx * deriv (fun w => F (w, y z)) (x z) +
        dy * deriv (fun w => F (x z, w)) (y z)) z := by
  have hu : HasDerivAt (fun w : ℂ => F (w, y z)) (L (1, 0)) (x z) := by
    simpa only [Function.comp_def, id_eq] using hF.comp_hasDerivAt (x z)
      ((hasDerivAt_id (x z)).prodMk (hasDerivAt_const (x z) (y z)))
  have hv : HasDerivAt (fun w : ℂ => F (x z, w)) (L (0, 1)) (y z) := by
    simpa only [Function.comp_def, id_eq] using hF.comp_hasDerivAt (y z)
      ((hasDerivAt_const (y z) (x z)).prodMk (hasDerivAt_id (y z)))
  have hL : L (dx, dy) = dx * L (1, 0) + dy * L (0, 1) := by
    have he : (dx, dy) = dx • ((1, 0) : ℂ × ℂ) + dy • ((0, 1) : ℂ × ℂ) := by
      ext <;> simp
    rw [he, map_add, map_smul, map_smul]
    rfl
  rw [hu.deriv, hv.deriv]
  simpa only [Function.comp_def, hL] using hF.comp_hasDerivAt z (hx.prodMk hy)

set_option maxHeartbeats 1600000 in
private lemma pathY_hasDerivAt (f square : Bool) (u v z : ℂ)
    (hu : 1 - u ≠ 0) (hx : 1 - z * u ≠ 0)
    (hd : pathDen f square u v z ≠ 0) :
    HasDerivAt (pathY f square u v)
      (velocity f square u (z * u) (pathY f square u v z)) z := by
  have ht := hasDerivAt_id z
  have hX : HasDerivAt (fun w : ℂ => 1 - w * u) (-u) z := by
    simpa using (ht.mul_const u).const_sub 1
  cases f <;> cases square
  · have hD : HasDerivAt (pathDen false false u v) 0 z :=
      hasDerivAt_const z (1 - u)
    have h := ((hX.const_mul (1 - v)).div hD hd).const_sub 1
    apply h.congr_deriv
    simp only [velocity, sigma, pathY, Bool.false_eq_true, ite_false, ite_true,
      id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
    generalize hDval : pathDen false false u v z = d at hd ⊢
    generalize hXval : z * u = x at hx ⊢
    field_simp [hd, hx]
    rw [← hDval, ← hXval]
    simp only [pathDen, Bool.false_eq_true, ite_false]
    ring
  · have hD : HasDerivAt (pathDen false true u v) (-u) z := hX
    have h := ((hasDerivAt_const z ((1 - v) * (1 - u))).div hD hd).const_sub 1
    apply h.congr_deriv
    simp only [velocity, sigma, pathY, Bool.false_eq_true, ite_false, ite_true,
      id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
    generalize hDval : pathDen false true u v z = d at hd ⊢
    generalize hXval : z * u = x at hx ⊢
    field_simp [hd, hx]
    rw [← hDval, ← hXval]
    simp only [pathDen, Bool.false_eq_true, ite_false, ite_true]
    ring
  · have hD : HasDerivAt (pathDen true false u v) (-(u * (1 - v))) z := by
      convert ((ht.add ((ht.const_sub 1).mul_const v)).const_mul u).const_sub 1 using 1 <;>
        (try funext w) <;> (try simp only [pathDen, ite_true, Bool.false_eq_true, ite_false, id_eq, Pi.add_apply]) <;> ring
    have h := (hasDerivAt_const z (v * (1 - u))).div hD hd
    apply h.congr_deriv
    simp only [velocity, sigma, pathY, Bool.false_eq_true, ite_false, ite_true,
      id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
    generalize hDval : pathDen true false u v z = d at hd ⊢
    generalize hXval : z * u = x at hx ⊢
    field_simp [hd, hx]
    rw [← hDval, ← hXval]
    simp only [pathDen, Bool.false_eq_true, ite_false, ite_true]
    ring
  · have hD : HasDerivAt (pathDen true true u v) (-(u * v)) z := by
      convert (((ht.mul_const v).const_add (1 - v)).const_mul u).const_sub 1 using 1 <;>
        (try funext w) <;> (try simp only [pathDen, ite_true, Bool.false_eq_true, ite_false, id_eq, Pi.add_apply]) <;> ring
    have h := (hX.const_mul v).div hD hd
    apply h.congr_deriv
    simp only [velocity, sigma, pathY, Bool.false_eq_true, ite_false, ite_true,
      id_eq, Pi.mul_apply, Pi.div_apply, Pi.sub_apply, Pi.add_apply]
    generalize hDval : pathDen true true u v z = d at hd ⊢
    generalize hXval : z * u = x at hx ⊢
    field_simp [hd, hx]
    rw [← hDval, ← hXval]
    simp only [pathDen, ite_true]
    ring

private lemma axis_zero {F : ℂ × ℂ → ℂ} {f square : Bool} {v : ℂ}
    (hpde : spatial false f square F 0 v = 0) (hm : modeScale f v ≠ 0) :
    F (0, v) = 0 := by
  have h : modeScale f v * (-(1 : ℂ) / 2 * F (0, v)) = 0 := by
    simpa [spatial, beta, modeScale] using hpde
  have h' := (mul_eq_zero.mp h).resolve_left hm
  exact (mul_eq_zero.mp h').resolve_left (by norm_num)

set_option maxHeartbeats 800000 in
private lemma ode_of_spatial (f square : Bool) (u z y A B H : ℂ)
    (hx : 1 - z * u ≠ 0) (hm : modeScale f y ≠ 0)
    (hpde : modeScale f y * (z * u * (1 - z * u) * A + beta false (z * u) * H) +
      sigma square * (z * u) * (y * (1 - y) * B + beta f y * H) = 0) :
    2 * z * (u * A + velocity f square u (z * u) y * B) =
      coefficient f square (z * u) y * H := by
  apply sub_eq_zero.mp
  calc
    _ = 2 * (modeScale f y * (z * u * (1 - z * u) * A + beta false (z * u) * H) +
        sigma square * (z * u) * (y * (1 - y) * B + beta f y * H)) /
          ((1 - z * u) * modeScale f y) := by
      cases f <;> cases square <;>
        simp only [velocity, coefficient, sigma, beta, modeScale,
          Bool.false_eq_true, ite_false, ite_true] at hm ⊢ <;>
        field_simp [hx, hm] <;> ring
    _ = 0 := by rw [hpde]; simp

private lemma gauge_hasDerivAt {f square : Bool} {u z : ℂ} {y : ℂ → ℂ} {dy : ℂ}
    (hy : HasDerivAt y dy z) (hm : modeScale f (y z) ≠ 0) :
    HasDerivAt (fun w => gaugeCore f square (w * u) (y w))
      (gaugePrime f square u (z * u) (y z) dy) z := by
  have hx := ((hasDerivAt_id z).mul_const u).const_sub 1
  have h1y := hy.const_sub 1
  cases f <;> cases square
  · change y z ≠ 0 at hm
    convert (hx.pow 4).div hy hm using 1 <;>
      (try funext w) <;>
      simp only [gaugeCore, gaugePrime, Bool.false_eq_true, ite_false, ite_true,
        Pi.pow_apply, Pi.mul_apply, Pi.div_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one] <;> ring
  · change y z ≠ 0 at hm
    convert (hasDerivAt_const z (1 : ℂ)).div hy hm using 1 <;>
      (try funext w) <;>
      simp only [gaugeCore, gaugePrime, Bool.false_eq_true, ite_false, ite_true,
        Pi.pow_apply, Pi.mul_apply, Pi.div_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one] <;> ring
  · convert hx.mul (h1y.pow 3) using 1 <;>
      (try funext w) <;>
      simp only [gaugeCore, gaugePrime, Bool.false_eq_true, ite_false, ite_true,
        Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one] <;> ring
  · convert (hx.pow 3).mul (h1y.pow 3) using 1 <;>
      (try funext w) <;>
      simp only [gaugeCore, gaugePrime, ite_true,
        Pi.pow_apply, Pi.mul_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one] <;> ring

set_option maxHeartbeats 800000 in
private lemma gauge_equation (f square : Bool) (u z y : ℂ)
    (hx : 1 - z * u ≠ 0) (hm : modeScale f y ≠ 0) :
    z * gaugePrime f square u (z * u) y (velocity f square u (z * u) y) =
      (1 - coefficient f square (z * u) y) * gaugeCore f square (z * u) y := by
  cases f <;> cases square <;>
    simp only [gaugePrime, gaugeCore, velocity, coefficient, sigma, beta, modeScale,
      Bool.false_eq_true, ite_false, ite_true] at hm ⊢ <;>
    field_simp [hx, hm] <;> ring

private lemma gauge_ne_zero (f square : Bool) (x y : ℂ)
    (hx : 1 - x ≠ 0) (hy : 1 - y ≠ 0) (hm : modeScale f y ≠ 0) :
    gaugeCore f square x y ≠ 0 := by
  cases f <;> cases square
  · exact div_ne_zero (pow_ne_zero 4 hx) hm
  · exact div_ne_zero one_ne_zero hm
  · exact mul_ne_zero hx (pow_ne_zero 3 hy)
  · exact mul_ne_zero (pow_ne_zero 3 hx) (pow_ne_zero 3 hy)

-- Removal at zero uses the forced value h(0)=0, not an assumed expansion.
private lemma continuousAt_sq_div_zero {h : ℂ → ℂ} {a : ℂ}
    (hd : HasDerivAt h a 0) (h0 : h 0 = 0) :
    ContinuousAt (fun z : ℂ => h z ^ 2 / z) 0 := by
  classical
  let q : ℂ → ℂ := Function.update (fun z => h z / z) 0 a
  have hq : ContinuousAt q 0 := by
    simpa only [q, h0, sub_zero] using hd.continuousAt_div
  have hc : ContinuousAt (fun z : ℂ => z * q z ^ 2) 0 :=
    continuousAt_id.mul (hq.pow 2)
  apply hc.congr
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z = 0
    · subst z
      simp [h0]
    · simp only [q, Function.update_of_ne hz]
      field_simp [hz] <;> ring

private lemma squared_gauge_derivative {h P : ℂ → ℂ} {z dh dP c : ℂ}
    (hz : z ≠ 0) (hh : HasDerivAt h dh z) (hP : HasDerivAt P dP z)
    (hode : 2 * z * dh = c * h z) (hgauge : z * dP = (1 - c) * P z) :
    HasDerivAt (fun w => h w ^ 2 * P w / w) 0 z := by
  have hn : (2 * h z * dh * P z + h z ^ 2 * dP) * z - h z ^ 2 * P z = 0 := by
    linear_combination h z * P z * hode + h z ^ 2 * hgauge
  have hd : HasDerivAt (fun w => h w ^ 2 * P w / w)
      (((2 * h z * dh * P z + h z ^ 2 * dP) * z - h z ^ 2 * P z) / z ^ 2) z := by
    convert ((hh.pow 2).mul hP).div (hasDerivAt_id z) hz using 1 <;>
      (try funext w) <;>
      (try simp only [Pi.pow_apply, Pi.mul_apply, Pi.div_apply, id_eq, Nat.cast_ofNat,
        Nat.reduceSub, pow_one]) <;> ring
  simpa only [hn, zero_div] using hd

private lemma endpoints_equal_of_derivative_zero {g : ℝ → ℂ}
    (hc : ContinuousOn g (Icc 0 1))
    (hd : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt g 0 t) : g 1 = g 0 := by
  have hdiff : DifferentiableOn ℝ g (Ioo 0 1) :=
    fun t ht => (hd t ht).differentiableAt.differentiableWithinAt
  have hzero : EqOn (deriv g) 0 (Ioo 0 1) := fun t ht => (hd t ht).deriv
  have hi : EqOn g (fun _ => g (1 / 2)) (Ioo (0 : ℝ) 1) := by
    intro t ht
    exact isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hzero ht
      (by norm_num)
  have he : EqOn g (fun _ => g (1 / 2)) (Icc (0 : ℝ) 1) :=
    hi.of_subset_closure hc continuousOn_const Ioo_subset_Icc_self (by
      simpa only [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)] using
        (Subset.rfl : Icc (0 : ℝ) 1 ⊆ Icc 0 1))
  exact (he (by norm_num : (1 : ℝ) ∈ Icc 0 1)).trans
    (he (by norm_num : (0 : ℝ) ∈ Icc 0 1)).symm

private lemma slice_zero_of_local_zero {g : ℂ → ℂ} {R rho : ℝ}
    (hR : 0 < R) (hrho : 0 < rho)
    (hd : ∀ u, ‖u‖ < R → DifferentiableAt ℂ g u)
    (hz : ∀ u, ‖u‖ < rho → g u = 0) : ∀ u, ‖u‖ < R → g u = 0 := by
  have hdiff : DifferentiableOn ℂ g (Metric.ball 0 R) := by
    intro u hu
    exact (hd u (by simpa using hu)).differentiableWithinAt
  have hlocal : g =ᶠ[𝓝 (0 : ℂ)] 0 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hrho] with u hu
    exact hz u (by simpa using hu)
  have he := (hdiff.analyticOnNhd Metric.isOpen_ball).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (convex_ball (0 : ℂ) R).isPreconnected (Metric.mem_ball_self hR) hlocal
  intro u hu
  exact he (by simpa using hu)

private lemma value_zero_of_punctured_disk {g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hc : ContinuousAt g 0)
    (hz : ∀ v, ‖v‖ < R → v ≠ 0 → g v = 0) : g 0 = 0 := by
  have hn : ∀ᶠ v in 𝓝[≠] (0 : ℂ), v ≠ 0 := self_mem_nhdsWithin
  have he : g =ᶠ[𝓝[≠] (0 : ℂ)] 0 := by
    filter_upwards [hn, (show ∀ᶠ v : ℂ in 𝓝[≠] (0 : ℂ), v ∈ Metric.ball 0 R from
        nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hR))] with v hv hvR
    exact hz v (by simpa using hvR) hv
  exact tendsto_nhds_unique_of_eventuallyEq
    (hc.tendsto.mono_left nhdsWithin_le_nhds) tendsto_const_nhds he

-- No hypothesis in this local lemma is an extra boundary value: hv0 only
-- selects the nonzero slices when f=false; the missing slice is restored below.
private theorem negative_first_local_zero {R : ℝ} (hR : R ≤ 1)
    (f square : Bool) (F : ℂ × ℂ → ℂ)
    (hreg : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → DifferentiableAt ℂ F (a, b))
    (hpde : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → spatial false f square F a b = 0)
    {u v : ℂ} (hv : ‖v‖ < R) (hv0 : f = false → v ≠ 0)
    (hu : ‖u‖ < radius R f v) : F (u, v) = 0 := by
  let y : ℂ → ℂ := pathY f square u v
  let P : ℂ → ℂ := pathGauge f square u v
  let h : ℂ → ℂ := fun z => F (z * u, y z)
  let dh : ℂ → ℂ := fun z =>
    u * deriv (fun w => F (w, y z)) (z * u) +
      velocity f square u (z * u) (y z) * deriv (fun w => F (z * u, w)) (y z)
  let dP : ℂ → ℂ := fun z =>
    gaugePrime f square u (z * u) (y z) (velocity f square u (z * u) (y z))
  let g : ℂ → ℂ := fun z => h z ^ 2 * P z / z
  have hdom (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : PathDomain R f square u v t :=
    path_domain hR hv hu ht
  have hy (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt y (velocity f square u ((t : ℂ) * u) (y (t : ℂ))) (t : ℂ) :=
    pathY_hasDerivAt f square u v (t : ℂ) (hdom t ht).u_ne
      (hdom t ht).x_ne (hdom t ht).den_ne
  have hh (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt h (dh (t : ℂ)) (t : ℂ) := by
    exact coordinate_chain (hreg _ _ (hdom t ht).x_mem (hdom t ht).y_mem).hasFDerivAt
      (by simpa using (hasDerivAt_id (t : ℂ)).mul_const u) (hy t ht)
  have hP (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      HasDerivAt P (dP (t : ℂ)) (t : ℂ) :=
    gauge_hasDerivAt (hy t ht) (hdom t ht).scale_ne
  have h0 : h 0 = 0 := by
    have hd0 := hdom 0 (by norm_num)
    have he := hpde 0 (y 0) (by simpa using hd0.x_mem) (by simpa using hd0.y_mem)
    have hm : modeScale f (y 0) ≠ 0 := by simpa using hd0.scale_ne
    simpa only [h, zero_mul] using axis_zero he hm
  have hc : ContinuousOn (fun t : ℝ => g (t : ℂ)) (Icc 0 1) := by
    intro t ht
    have hc' : ContinuousAt g (t : ℂ) := by
      by_cases ht0 : t = 0
      · subst t
        have hh0 : HasDerivAt h (dh 0) 0 := by simpa using hh 0 (by norm_num)
        have hP0 : ContinuousAt P 0 := by
          simpa using (hP 0 (by norm_num)).continuousAt
        have hr := (continuousAt_sq_div_zero hh0 h0).mul hP0
        have he : (fun z : ℂ => h z ^ 2 / z * P z) = g := by
          funext z
          dsimp [g]
          ring
        change ContinuousAt g 0
        rw [← he]
        exact hr
      · exact (((hh t ht).continuousAt.pow 2).mul (hP t ht).continuousAt).div
          continuousAt_id (by exact_mod_cast ht0)
    exact (hc'.comp (Complex.continuous_ofReal.continuousAt)).continuousWithinAt
  have hd (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (fun s : ℝ => g (s : ℂ)) 0 t := by
    have ht' := Ioo_subset_Icc_self ht
    have hz : (t : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt ht.1)
    have he := hpde _ _ (hdom t ht').x_mem (hdom t ht').y_mem
    have hode : 2 * (t : ℂ) * dh (t : ℂ) =
        coefficient f square ((t : ℂ) * u) (y (t : ℂ)) * h (t : ℂ) := by
      apply ode_of_spatial f square u (t : ℂ) (y (t : ℂ)) _ _ _
        (hdom t ht').x_ne (hdom t ht').scale_ne
      simpa only [spatial, modeScale, Bool.false_eq_true, ite_false] using he
    have hgauge : (t : ℂ) * dP (t : ℂ) =
        (1 - coefficient f square ((t : ℂ) * u) (y (t : ℂ))) * P (t : ℂ) :=
      gauge_equation f square u (t : ℂ) (y (t : ℂ))
        (hdom t ht').x_ne (hdom t ht').scale_ne
    exact (squared_gauge_derivative hz (hh t ht') (hP t ht') hode hgauge).comp_ofReal
  have hends := endpoints_equal_of_derivative_zero hc hd
  have hg1 : h 1 ^ 2 * P 1 = 0 := by
    simpa only [Complex.ofReal_one, Complex.ofReal_zero, g, div_one, div_zero] using hends
  have hd1 := hdom 1 (by norm_num)
  have hPend : P 1 ≠ 0 := by
    exact gauge_ne_zero f square (1 * u) (y 1)
      (by simpa using hd1.x_ne) (by simpa using hd1.y_ne_one)
      (by simpa using hd1.scale_ne)
  have hh1 : h 1 = 0 := eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hg1).resolve_right hPend)
  simpa only [h, one_mul, y, pathY_one f square u v hd1.u_ne] using hh1

private theorem negative_first_zero {R : ℝ} (hR0 : 0 < R) (hR : R ≤ 1)
    (f square : Bool) (F : ℂ × ℂ → ℂ)
    (hreg : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → DifferentiableAt ℂ F (a, b))
    (hpde : ∀ a b : ℂ, ‖a‖ < R → ‖b‖ < R → spatial false f square F a b = 0)
    {u v : ℂ} (hu : ‖u‖ < R) (hv : ‖v‖ < R) : F (u, v) = 0 := by
  have hgood (b : ℂ) (hb : ‖b‖ < R) (hb0 : f = false → b ≠ 0) :
      ∀ a : ℂ, ‖a‖ < R → F (a, b) = 0 := by
    apply slice_zero_of_local_zero hR0 (radius_pos hb hb0)
    · intro a ha
      exact ((hreg a b ha hb).comp a
        (differentiableAt_id.prodMk (differentiableAt_const b)))
    · intro a ha
      exact negative_first_local_zero hR f square F hreg hpde hb hb0 ha
  cases f
  · by_cases hv0 : v = 0
    · subst v
      apply value_zero_of_punctured_disk (g := fun b => F (u,b)) hR0
      · exact ((hreg u 0 hu (by simpa using hR0)).comp 0
          ((differentiableAt_const u).prodMk differentiableAt_id)).continuousAt
      · intro b hb hb0
        exact hgood b hb (fun _ => hb0) u hu
    · exact hgood v hv (fun _ => hv0) u hu
  · exact hgood v hv (by simp) u hu

private lemma spatial_swap (e f square : Bool) (F : ℂ × ℂ → ℂ) (u v : ℂ) :
    spatial f e square (fun p => F (p.2, p.1)) u v =
      sigma square * spatial e f square F v u := by
  cases square <;> simp only [spatial, sigma, Bool.false_eq_true, ite_false, ite_true] <;> ring

/-- Six-sector uniqueness on the entire open bidisk. false is the negative label;
false square is J and true square is T. There are no axis, expansion, boundary,
continuous-derivative or candidate-equality hypotheses. -/
theorem signed_spatial_zero {Rreal : ℝ} (hRpos : 0 < Rreal) (hRone : Rreal ≤ 1)
    (F : ℂ × ℂ → ℂ) (e f square : Bool) (hnegative : e = false ∨ f = false)
    (hdiff : ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal →
      DifferentiableAt ℂ F (u, v))
    (hpde : ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal →
      (if f then (1 : ℂ) else v) *
        (u * (1 - u) * deriv (fun w => F (w, v)) u +
          (if e then (1 - 3 * u) / 2 else -(1 + u) / 2) * F (u, v)) +
      (if square then (-1 : ℂ) else 1) * (if e then (1 : ℂ) else u) *
        (v * (1 - v) * deriv (fun w => F (u, w)) v +
          (if f then (1 - 3 * v) / 2 else -(1 + v) / 2) * F (u, v)) = 0) :
    ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal → F (u, v) = 0 := by
  have heq : ∀ u v : ℂ, ‖u‖ < Rreal → ‖v‖ < Rreal →
      spatial e f square F u v = 0 := hpde
  intro u v hu hv
  rcases hnegative with he | hf
  · subst e
    exact negative_first_zero hRpos hRone f square F hdiff heq hu hv
  · subst f
    let H : ℂ × ℂ → ℂ := fun p => F (p.2, p.1)
    have hHreg (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
        DifferentiableAt ℂ H (a, b) :=
      (hdiff b a hb ha).comp (a, b) (differentiableAt_snd.prodMk differentiableAt_fst)
    have hHpde (a b : ℂ) (ha : ‖a‖ < Rreal) (hb : ‖b‖ < Rreal) :
        spatial false e square H a b = 0 := by
      rw [spatial_swap e false square F a b, heq b a hb ha, mul_zero]
    exact negative_first_zero hRpos hRone e square H hHreg hHpde hv hu

end D5.S3.VertexAlgebra.TwistedGround.Signed.SpatialUniqueness
