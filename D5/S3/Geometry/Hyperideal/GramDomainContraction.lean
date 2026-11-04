/- GID: D5/S3/Geometry/Hyperideal/GramDomainContraction
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/GramDomainContraction
   mirror-E: none(waiver:explicit-gram-domain-contraction)
   anchors: []
   utility: none
   digest: An explicit two-stage contraction of the complete six-cosh negative-determinant Gram domain. -/

import D5.S3.Geometry.Hyperideal.OriginalCosineDeterminantInterface
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.Algebra.GroupWithZero

noncomputable section
open scoped Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace D5.S3.Geometry.Hyperideal.GramDomainContraction

/-- Edge order: 12, 13, 14, 34, 24, 23. -/
abbrev gram := OriginalCosineDeterminantInterface.gram

def delta (a b c d e f : ℝ) : ℝ := -(gram a b c d e f).det

private def triangleT (a b c d e f : ℝ) : ℝ :=
  a*b*f + a*c*e + b*c*d + d*e*f

private def c1 (a b c d e f : ℝ) : ℝ := 8*((a+d)+(b+e)+(c+f))
private def c2 (a b c d e f : ℝ) : ℝ :=
  4*((a+d)*(b+e)+(a+d)*(c+f)+(b+e)*(c+f))
private def c3 (a b c d e f : ℝ) : ℝ :=
  2*(triangleT a b c d e f + (a+d)*(b*e+c*f-a*d) +
     (b+e)*(a*d+c*f-b*e) + (c+f)*(a*d+b*e-c*f))
private def c4 (a b c d e f : ℝ) : ℝ :=
  2*((a*d)*(b*e)+(a*d)*(c*f)+(b*e)*(c*f)) -
    ((a*d)^2+(b*e)^2+(c*f)^2)

private theorem radial_expansion (a b c d e f s : ℝ) :
    delta (1+s*a) (1+s*b) (1+s*c) (1+s*d) (1+s*e) (1+s*f) =
      16 + c1 a b c d e f*s + c2 a b c d e f*s^2 +
        c3 a b c d e f*s^3 + c4 a b c d e f*s^4 := by
  simp [delta, gram, OriginalCosineDeterminantInterface.gram, Matrix.det_succ_row_zero, Matrix.det_fin_three,
    Matrix.det_fin_two, Matrix.det_fin_one, Matrix.det_fin_zero,
    Matrix.submatrix_apply, Fin.sum_univ_succ, Fin.succAbove]
  <;> unfold c1 c2 c3 c4 triangleT <;> ring

private theorem c3_swapAB (a b c d e f : ℝ) :
    c3 b a c e d f = c3 a b c d e f := by
  unfold c3 triangleT
  ring

private theorem c3_swapAC (a b c d e f : ℝ) :
    c3 c b a f e d = c3 a b c d e f := by
  unfold c3 triangleT
  ring

private theorem c4_swapAB (a b c d e f : ℝ) :
    c4 b a c e d f = c4 a b c d e f := by
  unfold c4
  ring

private theorem c4_swapAC (a b c d e f : ℝ) :
    c4 c b a f e d = c4 a b c d e f := by
  unfold c4
  ring

theorem twice_sqrt_product_le_add (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    2*Real.sqrt (u*v) ≤ u+v := by
  calc
    2*Real.sqrt (u*v) = 2*Real.sqrt u*Real.sqrt v := by
      rw [Real.sqrt_mul hu]
      ring
    _ ≤ (Real.sqrt u)^2+(Real.sqrt v)^2 := two_mul_le_add_sq _ _
    _ = u+v := by rw [Real.sq_sqrt hu, Real.sq_sqrt hv]

/-- The maximal opposite-pair case; no cubic-sign premise is supplied. -/
private theorem c3_nonneg_maxA (a b c d e f : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hAB : b*e ≤ a*d) (hAC : c*f ≤ a*d)
    (h4 : 0 ≤ c4 a b c d e f) : 0 ≤ c3 a b c d e f := by
  let r := Real.sqrt ((b*e)*(c*f))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = (b*e)*(c*f) :=
    Real.sq_sqrt (mul_nonneg (mul_nonneg hb he) (mul_nonneg hc hf))
  have hbfce := twice_sqrt_product_le_add (b*f) (c*e)
    (mul_nonneg hb hf) (mul_nonneg hc he)
  have hbcef := twice_sqrt_product_le_add (b*c) (e*f)
    (mul_nonneg hb hc) (mul_nonneg he hf)
  have hprod1 : (b*f)*(c*e) = (b*e)*(c*f) := by ring
  have hprod2 : (b*c)*(e*f) = (b*e)*(c*f) := by ring
  rw [hprod1] at hbfce
  rw [hprod2] at hbcef
  have ht1 := mul_le_mul_of_nonneg_left hbfce ha
  have ht2 := mul_le_mul_of_nonneg_left hbcef hd
  have ht : 2*(a+d)*r ≤ triangleT a b c d e f := by
    dsimp [r]
    unfold triangleT
    nlinarith only [ht1, ht2]
  have hdisc : (a*d-b*e-c*f)^2 ≤ 4*((b*e)*(c*f)) := by
    unfold c4 at h4
    nlinarith only [h4]
  have hupper : a*d-b*e-c*f ≤ 2*r := by
    have h := Real.le_sqrt_of_sq_le hdisc
    have heq : Real.sqrt (4*((b*e)*(c*f))) = 2*r := by
      apply (Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity)).2
      nlinarith only [hr2]
    rwa [heq] at h
  have hgap : 0 ≤ b*e+c*f-a*d+2*r := by linarith
  have hp := mul_nonneg (add_nonneg ha hd) hgap
  have hq := mul_nonneg (add_nonneg hb he)
    (show 0 ≤ a*d+c*f-b*e by nlinarith [mul_nonneg hc hf])
  have hrr := mul_nonneg (add_nonneg hc hf)
    (show 0 ≤ a*d+b*e-c*f by nlinarith [mul_nonneg hb he])
  unfold c3
  nlinarith only [ht, hp, hq, hrr]

/-- Cubic positivity is derived from the quartic sign for the same six coordinates. -/
private theorem cubic_nonneg_of_quartic_nonneg (a b c d e f : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) (hf : 0 ≤ f)
    (h4 : 0 ≤ c4 a b c d e f) : 0 ≤ c3 a b c d e f := by
  by_cases hAB : b*e ≤ a*d
  · by_cases hAC : c*f ≤ a*d
    · exact c3_nonneg_maxA a b c d e f ha hb hc hd he hf hAB hAC h4
    · have hCA : a*d ≤ c*f := (lt_of_not_ge hAC).le
      have hCB : b*e ≤ c*f := hAB.trans hCA
      have h4' : 0 ≤ c4 c b a f e d := by rwa [c4_swapAC]
      have h := c3_nonneg_maxA c b a f e d hc hb ha hf he hd hCB hCA h4'
      rwa [c3_swapAC] at h
  · have hBA : a*d ≤ b*e := (lt_of_not_ge hAB).le
    by_cases hBC : c*f ≤ b*e
    · have h4' : 0 ≤ c4 b a c e d f := by rwa [c4_swapAB]
      have h := c3_nonneg_maxA b a c e d f hb ha hc he hd hf hBA hBC h4'
      rwa [c3_swapAB] at h
    · have hCB : b*e ≤ c*f := (lt_of_not_ge hBC).le
      have hCA : a*d ≤ c*f := hBA.trans hCB
      have h4' : 0 ≤ c4 c b a f e d := by rwa [c4_swapAC]
      have h := c3_nonneg_maxA c b a f e d hc hb ha hf he hd hCB hCA h4'
      rwa [c3_swapAC] at h

/-- Quantitative radial bound in the actual six-entry Gram determinant. -/
private theorem radial_delta_lower_bound (a b c d e f s : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    min 16 (delta a b c d e f) ≤
      delta (1+s*(a-1)) (1+s*(b-1)) (1+s*(c-1))
        (1+s*(d-1)) (1+s*(e-1)) (1+s*(f-1)) := by
  have ha0 : 0 ≤ a-1 := sub_nonneg.mpr ha
  have hb0 : 0 ≤ b-1 := sub_nonneg.mpr hb
  have hc0 : 0 ≤ c-1 := sub_nonneg.mpr hc
  have hd0 : 0 ≤ d-1 := sub_nonneg.mpr hd
  have he0 : 0 ≤ e-1 := sub_nonneg.mpr he
  have hf0 : 0 ≤ f-1 := sub_nonneg.mpr hf
  let A := c1 (a-1) (b-1) (c-1) (d-1) (e-1) (f-1)
  let B := c2 (a-1) (b-1) (c-1) (d-1) (e-1) (f-1)
  let C := c3 (a-1) (b-1) (c-1) (d-1) (e-1) (f-1)
  let D := c4 (a-1) (b-1) (c-1) (d-1) (e-1) (f-1)
  have hA : 0 ≤ A := by dsimp [A, c1]; positivity
  have hB : 0 ≤ B := by dsimp [B, c2]; positivity
  have hexp := radial_expansion (a-1) (b-1) (c-1) (d-1) (e-1) (f-1) s
  change delta (1+s*(a-1)) (1+s*(b-1)) (1+s*(c-1))
      (1+s*(d-1)) (1+s*(e-1)) (1+s*(f-1)) =
        16+A*s+B*s^2+C*s^3+D*s^4 at hexp
  have hone : delta a b c d e f = 16+A+B+C+D := by
    simpa [A, B, C, D] using
      radial_expansion (a-1) (b-1) (c-1) (d-1) (e-1) (f-1) 1
  rw [hexp]
  by_cases hD : 0 ≤ D
  · have hC : 0 ≤ C := cubic_nonneg_of_quartic_nonneg
      (a-1) (b-1) (c-1) (d-1) (e-1) (f-1)
      (sub_nonneg.mpr ha) (sub_nonneg.mpr hb) (sub_nonneg.mpr hc)
      (sub_nonneg.mpr hd) (sub_nonneg.mpr he) (sub_nonneg.mpr hf) hD
    have hsum : 0 ≤ A*s+B*s^2+C*s^3+D*s^4 :=
      add_nonneg
        (add_nonneg (add_nonneg (mul_nonneg hA hs0) (mul_nonneg hB (sq_nonneg s)))
          (mul_nonneg hC (pow_nonneg hs0 3)))
        (mul_nonneg hD (pow_nonneg hs0 4))
    exact (min_le_left 16 (delta a b c d e f)).trans (by linarith only [hsum])
  · have hDn : D ≤ 0 := (lt_of_not_ge hD).le
    have hs3 : 0 ≤ s^3 := pow_nonneg hs0 _
    have hm : 0 ≤ 1-s := sub_nonneg.mpr hs1
    have ht0 : 0 ≤ 1-s^3 := by
      have hp := mul_nonneg hm (show 0 ≤ 1+s+s^2 by positivity)
      nlinarith only [hp]
    have ht1 : 0 ≤ s-s^3 := by
      have hp := mul_nonneg (mul_nonneg hs0 hm) (show 0 ≤ 1+s by positivity)
      nlinarith only [hp]
    have ht2 : 0 ≤ s^2-s^3 := by
      have hp := mul_nonneg (sq_nonneg s) hm
      nlinarith only [hp]
    have ht4 : s^4-s^3 ≤ 0 := by
      have hp := mul_nonpos_of_nonneg_of_nonpos hs3 (show s-1 ≤ 0 by linarith)
      nlinarith only [hp]
    have hprod1 := mul_nonneg hA ht1
    have hprod2 := mul_nonneg hB ht2
    have hprod4 := mul_nonneg_of_nonpos_of_nonpos hDn ht4
    have hcompare : 16*(1-s^3)+s^3*(delta a b c d e f) ≤
        16+A*s+B*s^2+C*s^3+D*s^4 := by
      rw [hone]
      nlinarith only [hprod1, hprod2, hprod4]
    have hm0 := mul_le_mul_of_nonneg_right (min_le_left 16 (delta a b c d e f)) ht0
    have hm1 := mul_le_mul_of_nonneg_right (min_le_right 16 (delta a b c d e f)) hs3
    nlinarith only [hm0, hm1, hcompare]

end D5.S3.Geometry.Hyperideal.GramDomainContraction

end

noncomputable section
open Set
open scoped Topology

namespace D5.S3.Geometry.Hyperideal.GramDomainContraction


abbrev Coordinates := Fin 6 → ℝ

def Delta (x : Coordinates) : ℝ := delta (x 0) (x 1) (x 2) (x 3) (x 4) (x 5)

def rawDomain : Set Coordinates := {x | (∀ i, 1 < x i) ∧ 0 < Delta x}

abbrev X := {x : Coordinates // x ∈ rawDomain}

private theorem product_unit_bounds (a b : ℝ) (ha : 0 ≤ a ∧ a ≤ 1)
    (hb : 0 ≤ b ∧ b ≤ 1) : 0 ≤ a * b ∧ a * b ≤ 1 := by
  refine ⟨mul_nonneg ha.1 hb.1, ?_⟩
  exact (mul_le_mul_of_nonneg_left hb.2 ha.1).trans (by simpa using ha.2)

private theorem square_unit_bound (a : ℝ) (ha : 0 ≤ a ∧ a ≤ 1) : a ^ 2 ≤ 1 := by
  nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr ha.2)]

/-- The explicit 16 - 12 - 3 certificate on the full closed unit cube. -/
private theorem cube_delta_lower_bound (a b c d e f : ℝ)
    (ha : 0 ≤ a ∧ a ≤ 1) (hb : 0 ≤ b ∧ b ≤ 1)
    (hc : 0 ≤ c ∧ c ≤ 1) (hd : 0 ≤ d ∧ d ≤ 1)
    (he : 0 ≤ e ∧ e ≤ 1) (hf : 0 ≤ f ∧ f ≤ 1) :
    1 ≤ delta (1+a) (1+b) (1+c) (1+d) (1+e) (1+f) := by
  have hU := product_unit_bounds a d ha hd
  have hV := product_unit_bounds b e hb he
  have hW := product_unit_bounds c f hc hf
  have hU2 := square_unit_bound (a*d) hU
  have hV2 := square_unit_bound (b*e) hV
  have hW2 := square_unit_bound (c*f) hW
  have hp : 0 ≤ a+d := add_nonneg ha.1 hd.1
  have hq : 0 ≤ b+e := add_nonneg hb.1 he.1
  have hr : 0 ≤ c+f := add_nonneg hc.1 hf.1
  have hpU : (a+d)*(a*d) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hU.2 hp).trans (by nlinarith [ha.2, hd.2])
  have hqV : (b+e)*(b*e) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hV.2 hq).trans (by nlinarith [hb.2, he.2])
  have hrW : (c+f)*(c*f) ≤ 2 :=
    (mul_le_mul_of_nonneg_left hW.2 hr).trans (by nlinarith [hc.2, hf.2])
  have ha0 := ha.1
  have hb0 := hb.1
  have hc0 := hc.1
  have hd0 := hd.1
  have he0 := he.1
  have hf0 := hf.1
  have hT : 0 ≤ triangleT a b c d e f := by
    unfold triangleT
    positivity
  have hpositive : 0 ≤ triangleT a b c d e f +
      (a+d)*(b*e+c*f) + (b+e)*(a*d+c*f) + (c+f)*(a*d+b*e) := by
    positivity
  have h3 : -12 ≤ c3 a b c d e f := by
    unfold c3
    nlinarith only [hpositive, hpU, hqV, hrW]
  have hpairs : 0 ≤ (a*d)*(b*e)+(a*d)*(c*f)+(b*e)*(c*f) := by positivity
  have h4 : -3 ≤ c4 a b c d e f := by
    unfold c4
    nlinarith only [hpairs, hU2, hV2, hW2]
  have h1 : 0 ≤ c1 a b c d e f := by unfold c1; positivity
  have h2 : 0 ≤ c2 a b c d e f := by unfold c2; positivity
  have hexp : delta (1+a) (1+b) (1+c) (1+d) (1+e) (1+f) =
      16 + c1 a b c d e f + c2 a b c d e f +
        c3 a b c d e f + c4 a b c d e f := by
    simpa using radial_expansion a b c d e f 1
  linarith

private theorem cube_Delta_lower_bound (y : Coordinates)
    (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) : 1 ≤ Delta (fun i => 1+y i) :=
  cube_delta_lower_bound _ _ _ _ _ _ (hy 0) (hy 1) (hy 2) (hy 3) (hy 4) (hy 5)

def center : X := ⟨fun _ => 2, by
  refine ⟨fun _ => by norm_num, ?_⟩
  have h := cube_Delta_lower_bound (fun _ => 1) (fun _ => by norm_num)
  exact lt_of_lt_of_le (show (0 : ℝ) < 1 by norm_num)
    (by simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using h)⟩

/-- M = max(1, x0-1, ..., x5-1), expressed by a fixed finite max tree. -/
private def maximum (x : X) : ℝ :=
  max 1 (max (x.val 0-1) (max (x.val 1-1) (max (x.val 2-1)
    (max (x.val 3-1) (max (x.val 4-1) (x.val 5-1))))))

private theorem one_le_maximum (x : X) : 1 ≤ maximum x := le_max_left _ _

private theorem coordinate_le_maximum (x : X) (i : Fin 6) : x.val i-1 ≤ maximum x := by
  fin_cases i <;> simp [maximum, le_max_iff]

private def eta (x : X) : ℝ := (maximum x)⁻¹

private theorem eta_bounds (x : X) : 0 < eta x ∧ eta x ≤ 1 := by
  have hm : 0 < maximum x := lt_of_lt_of_le zero_lt_one (one_le_maximum x)
  refine ⟨inv_pos.mpr hm, ?_⟩
  exact (inv_le_one₀ hm).2 (one_le_maximum x)

private theorem compressed_bounds (x : X) (i : Fin 6) :
    0 < eta x * (x.val i-1) ∧ eta x * (x.val i-1) ≤ 1 := by
  have hm : 0 < maximum x := lt_of_lt_of_le zero_lt_one (one_le_maximum x)
  refine ⟨mul_pos (eta_bounds x).1 (sub_pos.mpr (x.property.1 i)), ?_⟩
  simpa [eta, div_eq_mul_inv, mul_comm] using
    (div_le_one hm).2 (coordinate_le_maximum x i)

private theorem continuous_maximum : Continuous maximum := by
  have hcoord (i : Fin 6) : Continuous (fun x : X => x.val i-1) :=
    ((continuous_apply i).comp continuous_subtype_val).sub continuous_const
  unfold maximum
  exact continuous_const.max
    ((hcoord 0).max ((hcoord 1).max ((hcoord 2).max
      ((hcoord 3).max ((hcoord 4).max (hcoord 5))))))

private theorem continuous_eta : Continuous eta :=
  continuous_maximum.inv₀ (fun x =>
    (lt_of_lt_of_le zero_lt_one (one_le_maximum x)).ne')

private def radial (x : X) (s : ℝ) : Coordinates := fun i => 1+s*(x.val i-1)

private theorem radial_lower_bound (x : X) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    min 16 (Delta x.val) ≤ Delta (radial x s) :=
  radial_delta_lower_bound _ _ _ _ _ _ s
    (x.property.1 0).le (x.property.1 1).le (x.property.1 2).le
    (x.property.1 3).le (x.property.1 4).le (x.property.1 5).le hs0 hs1

private theorem radial_mem (x : X) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1) :
    radial x s ∈ rawDomain := by
  refine ⟨fun i => ?_, ?_⟩
  · have h := mul_pos hs0 (sub_pos.mpr (x.property.1 i))
    change 1 < 1+s*(x.val i-1)
    linarith
  · exact lt_of_lt_of_le (lt_min (by norm_num) x.property.2)
      (radial_lower_bound x s hs0.le hs1)

def compression : C(X, X) where
  toFun x := ⟨radial x (eta x), radial_mem x (eta x) (eta_bounds x).1 (eta_bounds x).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    exact continuous_const.add (continuous_eta.mul
      (((continuous_apply i).comp continuous_subtype_val).sub continuous_const))

private def radialScale (t : unitInterval) (x : X) : ℝ :=
  1-(t:ℝ)*(1-eta x)

private theorem radialScale_bounds (t : unitInterval) (x : X) :
    0 < radialScale t x ∧ radialScale t x ≤ 1 := by
  have he := eta_bounds x
  have ht := t.property
  have hlow := mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr he.2)
  have hupp := mul_nonneg ht.1 (sub_nonneg.mpr he.2)
  dsimp [radialScale]
  constructor <;> nlinarith

def radialHomotopy : (ContinuousMap.id X).Homotopy compression where
  toFun z := ⟨radial z.2 (radialScale z.1 z.2),
    radial_mem z.2 _ (radialScale_bounds z.1 z.2).1 (radialScale_bounds z.1 z.2).2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun z : unitInterval × X =>
      1+(1-(z.1:ℝ)*(1-eta z.2))*(z.2.val i-1))
    have heta : Continuous (fun z : unitInterval × X => eta z.2) :=
      continuous_eta.comp continuous_snd
    have ht : Continuous (fun z : unitInterval × X => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun z : unitInterval × X => z.2.val i - 1) :=
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd).sub continuous_const
    exact continuous_const.add
      ((continuous_const.sub (ht.mul (continuous_const.sub heta))).mul hx)
  map_zero_left x := by
    apply Subtype.ext
    funext i
    change 1+(1-(0:ℝ)*(1-eta x))*(x.val i-1) = x.val i
    ring
  map_one_left x := by
    apply Subtype.ext
    funext i
    change 1+(1-(1:ℝ)*(1-eta x))*(x.val i-1) = 1+eta x*(x.val i-1)
    ring

private def cubeOffset (t : unitInterval) (x : X) : Coordinates :=
  fun i => (1-(t:ℝ))*(eta x*(x.val i-1))+(t:ℝ)

private theorem cubeOffset_bounds (t : unitInterval) (x : X) (i : Fin 6) :
    0 < cubeOffset t x i ∧ cubeOffset t x i ≤ 1 := by
  have hb := compressed_bounds x i
  have ht := t.property
  have hp := mul_nonneg (sub_nonneg.mpr ht.2) hb.1.le
  have hu := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr ht.2)
  dsimp [cubeOffset]
  constructor
  · by_cases hz : (t:ℝ)=0
    · simpa [hz] using hb.1
    · have htp : 0 < (t:ℝ) := lt_of_le_of_ne ht.1 (Ne.symm hz)
      linarith
  · nlinarith

private theorem cube_mem (t : unitInterval) (x : X) :
    (fun i => 1+cubeOffset t x i) ∈ rawDomain := by
  refine ⟨fun i => by have h := (cubeOffset_bounds t x i).1; linarith, ?_⟩
  exact lt_of_lt_of_le (by norm_num)
    (cube_Delta_lower_bound (cubeOffset t x) (fun i =>
      ⟨(cubeOffset_bounds t x i).1.le, (cubeOffset_bounds t x i).2⟩))

def cubeHomotopy : compression.Homotopy (ContinuousMap.const X center) where
  toFun z := ⟨fun i => 1+cubeOffset z.1 z.2 i, cube_mem z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro i
    change Continuous (fun z : unitInterval × X =>
      1+((1-(z.1:ℝ))*(eta z.2*(z.2.val i-1))+(z.1:ℝ)))
    have heta : Continuous (fun z : unitInterval × X => eta z.2) :=
      continuous_eta.comp continuous_snd
    have ht : Continuous (fun z : unitInterval × X => (z.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun z : unitInterval × X => z.2.val i - 1) :=
      (((continuous_apply i).comp continuous_subtype_val).comp continuous_snd).sub continuous_const
    exact continuous_const.add (((continuous_const.sub ht).mul (heta.mul hx)).add ht)
  map_zero_left x := by
    apply Subtype.ext
    funext i
    change 1+((1-(0:ℝ))*(eta x*(x.val i-1))+0) = 1+eta x*(x.val i-1)
    ring
  map_one_left x := by
    apply Subtype.ext
    funext i
    change 1+((1-(1:ℝ))*(eta x*(x.val i-1))+1) = 2
    ring

/-- Explicit id-to-constant contraction of the entire raw domain. -/
def contraction : (ContinuousMap.id X).Homotopy (ContinuousMap.const X center) :=
  radialHomotopy.trans cubeHomotopy

/-- The full positive-cosh, negative-determinant parameter domain is contractible. -/
theorem full_domain_contractible : ContractibleSpace X := by
  apply (contractible_iff_id_nullhomotopic X).2
  exact ⟨center, ⟨contraction⟩⟩

end D5.S3.Geometry.Hyperideal.GramDomainContraction

end

#print axioms D5.S3.Geometry.Hyperideal.GramDomainContraction.full_domain_contractible
