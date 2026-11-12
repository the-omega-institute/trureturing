/- GID: D5/S3/Quantum/Recovery/FourPathTriangleFibre
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathTriangleFibre
   mirror-E: none(waiver:closed-triangle-fibre-geometry)
   anchors: []
   utility: none
   digest: The original triangle radicals satisfy a coupled fibre support inequality, including degenerate boundaries. -/

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathTriangleFibre
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.longLine false
set_option linter.style.whitespace false

/-- The complete attained triangle, with its closed box constraints. -/
def Triangle (L X Y : ℝ) : Prop :=
  0 ≤ X ∧ X ≤ 1 ∧ 0 ≤ Y ∧ Y ≤ 1 ∧ L ≤ Real.sqrt X + Real.sqrt Y

/-- The original normalized trace coordinate. -/
def Z (L X Y : ℝ) : ℝ := (L^2-X-Y)/(2*Real.sqrt (X*Y))

/-- The original nonnegative fibre radical. -/
def F (L X Y : ℝ) : ℝ := Real.sqrt ((1-X)*(1-Y)*(1-Z L X Y^2))

/-- The two geometric caps and the central fibre width. -/
def B (u : ℝ) : ℝ := (2-u)^2
def D (a u : ℝ) : ℝ := a*(2*u-a)
def W (a u : ℝ) : ℝ := B u*D a u/u^2

/-- A slightly relaxed low-half tangent, and the exact high-half chord cap. -/
def T (a u : ℝ) : ℝ := if u ≤ 1 then W a u else min (B u) (D a u)

private theorem geometry (L X Y : ℝ) (hL : 1 < L) (hL2 : L^2 ≤ 2)
    (h : Triangle L X Y) :
    0 < X ∧ 0 < Y ∧ 0 < X+Y ∧
    (Y-X)^2 < (X+Y)^2 ∧
    (Y-X)^2 ≤ B (X+Y) ∧ (Y-X)^2 ≤ D (L^2) (X+Y) ∧
    Z L X Y^2 ≤ 1 ∧
    4*(F L X Y)^2*((X+Y)^2-(Y-X)^2) =
      (B (X+Y)-(Y-X)^2)*(D (L^2) (X+Y)-(Y-X)^2) := by
  obtain ⟨hX,hX1,hY,hY1,htri⟩ := h
  have sx := Real.sq_sqrt hX
  have sy := Real.sq_sqrt hY
  have sx0 := Real.sqrt_nonneg X
  have sy0 := Real.sqrt_nonneg Y
  have sx1 : Real.sqrt X ≤ 1 := Real.sqrt_le_one.mpr hX1
  have sy1 : Real.sqrt Y ≤ 1 := Real.sqrt_le_one.mpr hY1
  have Xp : 0 < X := Real.sqrt_pos.mp (by linarith)
  have Yp : 0 < Y := Real.sqrt_pos.mp (by linarith)
  have xy : 0 < X*Y := mul_pos Xp Yp
  have rootp : 0 < Real.sqrt (X*Y) := Real.sqrt_pos.mpr xy
  have root2 := Real.sq_sqrt xy.le
  have rootmul : Real.sqrt (X*Y)=Real.sqrt X*Real.sqrt Y := Real.sqrt_mul hX Y
  have sumsq : L^2 ≤ X+Y+2*Real.sqrt (X*Y) := by
    rw [rootmul]
    nlinarith [sq_nonneg (Real.sqrt X+Real.sqrt Y-L)]
  have diff : X+Y-2*Real.sqrt (X*Y) ≤ 1 := by
    rw [rootmul]
    have hd : -1 ≤ Real.sqrt X-Real.sqrt Y := by linarith
    have hd' : Real.sqrt X-Real.sqrt Y ≤ 1 := by linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-(Real.sqrt X-Real.sqrt Y))
      (by linarith : 0 ≤ 1+(Real.sqrt X-Real.sqrt Y))]
  have L2 : 1 < L^2 := by nlinarith
  have zsq : (L^2-X-Y)^2 ≤ 4*(X*Y) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2*Real.sqrt (X*Y)-(L^2-X-Y))
      (by linarith : 0 ≤ 2*Real.sqrt (X*Y)+(L^2-X-Y))]
  have zi : Z L X Y*(2*Real.sqrt (X*Y))=L^2-X-Y := by
    unfold Z
    exact div_mul_cancel₀ _ (by positivity)
  have zid : (Z L X Y)^2*(4*(X*Y))=(L^2-X-Y)^2 := by
    nlinarith only [congrArg (fun t : ℝ => t^2) zi,root2]
  have zle : Z L X Y^2 ≤ 1 := by
    have : (Z L X Y^2-1)*(4*(X*Y)) ≤ 0 := by nlinarith only [zid,zsq]
    exact le_of_sub_nonpos ((mul_nonpos_iff_of_pos_right (by positivity : 0 < 4*(X*Y))).mp this)
  have fsq : (F L X Y)^2=(1-X)*(1-Y)*(1-Z L X Y^2) := by
    unfold F
    exact Real.sq_sqrt (mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith))
  have box : (Y-X)^2 ≤ B (X+Y) := by
    dsimp [B]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1-X) (by linarith : 0 ≤ 1-Y)]
  have diag : (Y-X)^2 ≤ D (L^2) (X+Y) := by
    dsimp [D]
    nlinarith only [zsq]
  refine ⟨Xp,Yp,by positivity,by nlinarith only [xy],box,diag,zle,?_⟩
  calc
    4*(F L X Y)^2*((X+Y)^2-(Y-X)^2) =
        4*((1-X)*(1-Y))*(4*(X*Y)-(L^2-X-Y)^2) := by
      rw [fsq]
      nlinarith only [congrArg (fun t : ℝ => 4*((1-X)*(1-Y))*t) zid]
    _ = _ := by unfold B D; ring

private lemma low_fibre (a u r f : ℝ) (hu : 0 < u) (hu1 : u ≤ 1)
    (hr : 0 ≤ r) (hru : r < u^2)
    (hf : f*(u^2-r)=(B u-r)*(D a u-r)) :
    r+f ≤ W a u := by
  have cap : D a u ≤ u^2 := by unfold D; nlinarith [sq_nonneg (u-a)]
  have cap' : u^2 ≤ B u := by unfold B; nlinarith
  have wid : W a u*u^2=B u*D a u := by
    unfold W
    exact div_mul_cancel₀ _ (by positivity)
  have identity : (W a u-r-f)*u^2*(u^2-r)=r*(B u-u^2)*(u^2-D a u) := by
    nlinarith only [congrArg (fun t : ℝ => t*(u^2-r)) wid,
      congrArg (fun t : ℝ => t*u^2) hf]
  have nn := mul_nonneg (mul_nonneg hr (sub_nonneg.mpr cap')) (sub_nonneg.mpr cap)
  have nn' : 0 ≤ W a u-r-f := by
    apply nonneg_of_mul_nonneg_right _ (sub_pos.mpr hru)
    apply nonneg_of_mul_nonneg_right _ (sq_pos_of_pos hu)
    nlinarith only [identity,nn]
  linarith

private lemma chord_fibre (U b d r f w : ℝ) (hU : 0 < U)
    (hb : 0 ≤ b) (hr : 0 ≤ r) (hrb : r ≤ b) (hru : r < U)
    (hd : d ≤ U) (hw : w*U=b*d) (hf : f*(U-r)=(b-r)*(d-r)) :
    w*r+b*f ≤ b*w := by
  have identity : (b*w-w*r-b*f)*U*(U-r)=b*r*(b-r)*(U-d) := by
    nlinarith only [congrArg (fun t : ℝ => t*(b-r)*(U-r)) hw,
      congrArg (fun t : ℝ => t*(b*U)) hf]
  have nn : 0 ≤ b*r*(b-r)*(U-d) := by positivity
  have nn' : 0 ≤ b*w-w*r-b*f := by
    apply nonneg_of_mul_nonneg_right _ (sub_pos.mpr hru)
    apply nonneg_of_mul_nonneg_right _ hU
    nlinarith only [identity,nn]
  linarith

/-- A closed fibre inequality for the actual radical, without division by a
possibly vanishing fibre width. -/
theorem closed_triangle_fibre (L X Y : ℝ) (hL : 1 < L) (hL2 : L^2 ≤ 2)
    (h : Triangle L X Y) :
    let u := X+Y
    let a := L^2
    0 ≤ T a u ∧ 0 ≤ W a u ∧
      W a u*(Y-X)^2+T a u*(2*F L X Y)^2 ≤ T a u*W a u := by
  dsimp only
  obtain ⟨Xp,Yp,up,tru,tB,tD,zle,fi⟩ := geometry L X Y hL hL2 h
  let u := X+Y
  let a := L^2
  let r := (Y-X)^2
  let f := (2*F L X Y)^2
  have bn : 0 ≤ B u := sq_nonneg _
  have dn : 0 ≤ D a u := (sq_nonneg (Y-X)).trans tD
  have wn : 0 ≤ W a u := div_nonneg (mul_nonneg bn dn) (sq_nonneg _)
  have wid : W a u*u^2=B u*D a u := by
    unfold W
    exact div_mul_cancel₀ _ (by positivity)
  have fidentity : f*(u^2-r)=(B u-r)*(D a u-r) := by
    dsimp [f,u,r,a]
    nlinarith only [fi]
  change 0 ≤ T a u ∧ 0 ≤ W a u ∧ W a u*r+T a u*f ≤ T a u*W a u
  by_cases hu1 : u ≤ 1
  · rw [T,if_pos hu1]
    have low := low_fibre a u r f up hu1 (sq_nonneg _) tru fidentity
    exact ⟨wn,wn,by nlinarith only [mul_le_mul_of_nonneg_left low wn]⟩
  · have bcap : B u ≤ u^2 := by unfold B; nlinarith
    have dcap : D a u ≤ u^2 := by unfold D; nlinarith [sq_nonneg (u-a)]
    rw [T,if_neg hu1]
    refine ⟨le_min bn dn,wn,?_⟩
    rcases le_total (B u) (D a u) with hbd | hdb
    · rw [min_eq_left hbd]
      exact chord_fibre (u^2) (B u) (D a u) r f (W a u)
        (sq_pos_of_pos up) bn (sq_nonneg _) tB tru dcap wid fidentity
    · rw [min_eq_right hdb]
      apply chord_fibre (u^2) (D a u) (B u) r f (W a u)
        (sq_pos_of_pos up) dn (sq_nonneg _) tD tru bcap
      · nlinarith only [wid]
      · nlinarith only [fidentity]

end D5.S3.Quantum.Recovery.FourPathTriangleFibre
