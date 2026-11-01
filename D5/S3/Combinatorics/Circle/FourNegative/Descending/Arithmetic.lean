/- GID: D5/S3/Combinatorics/Circle/FourNegative/Descending/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-estimates-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-estimates)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Six reserve bounds and their paired seam and peak consequences. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Schedule

/-! Uniform reserve inequalities for the entire descending chamber. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.Descending

set_option maxHeartbeats 1800000 in
private theorem reserve_bounds (x y z t h u v : ℤ)
    (ht : 4 ≤ t) (hz : 2*t ≤ z) (hy : z ≤ y) (hx : 2*y ≤ x)
    (hh : 1 ≤ h) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (ex : 4*t*h = x) (eu : 2*z*u = x) (ev : 2*y*v = x) :
    let D := 1+y+y*z
    let A := x*D+1
    let B := t*(1+x+x*y)+1
    let L := t*z*(1+x)+1+z
    let M := t*y*z+D
    let J := 2*M-D
    0 ≤ A-3*h*M ∧ 0 ≤ B-u*M ∧ 0 ≤ L-v*M ∧
    0 ≤ 2*(3*h)*J-3*A-1 ∧ 0 ≤ u*J-B ∧ 0 ≤ 2*v*J-(2*L-1-z)-1 ∧
    0 ≤ 2*A-3*h*J ∧ 0 ≤ (2*B-1)-u*J ∧ 0 ≤ (2*L-1-z)-v*J ∧
    0 ≤ 2*(3*h)*M-A-1 ∧ 0 ≤ 2*u*M-B-1 ∧ 0 ≤ 2*v*M-L-1 := by
  dsimp only
  let D := 1+y+y*z
  let A := x*D+1
  let B := t*(1+x+x*y)+1
  let L := t*z*(1+x)+1+z
  let M := t*y*z+D
  let J := 2*M-D
  change 0 ≤ A-3*h*M ∧ 0 ≤ B-u*M ∧ 0 ≤ L-v*M ∧
    0 ≤ 2*(3*h)*J-3*A-1 ∧ 0 ≤ u*J-B ∧ 0 ≤ 2*v*J-(2*L-1-z)-1 ∧
    0 ≤ 2*A-3*h*J ∧ 0 ≤ (2*B-1)-u*J ∧ 0 ≤ (2*L-1-z)-v*J ∧
    0 ≤ 2*(3*h)*M-A-1 ∧ 0 ≤ 2*u*M-B-1 ∧ 0 ≤ 2*v*M-L-1
  have ht0 : 0 ≤ t := by omega
  have hz0 : 0 ≤ z := by omega
  have hy0 : 0 ≤ y := by omega
  have hx0 : 0 ≤ x := by omega
  have hxt : 4*t ≤ x := by omega
  have hyz : y+1 ≤ y*z := by nlinarith [mul_nonneg (by omega : 0 ≤ y-1) (by omega : 0 ≤ z-2)]
  have hc : 0 ≤ (t-1)*y*z-y-1 := by
    have hn := mul_nonneg (by omega : 0 ≤ t-2) (mul_nonneg hy0 hz0)
    nlinarith only [hn,hyz]
  have s0id : 4*t*(A-3*h*M) = x*((t-3)*y*z+(4*t-3)*(y+1))+4*t := by
    dsimp [A,M,D]; rw [←ex]; ring
  have s0rhs : 0 ≤ x*((t-3)*y*z+(4*t-3)*(y+1))+4*t := by
    have h1 : 0 ≤ t-3 := by omega
    have h2 : 0 ≤ 4*t-3 := by omega
    positivity
  have s0 : 0 ≤ A-3*h*M := by
    apply (mul_nonneg_iff_of_pos_left (by omega : 0 < 4*t)).mp
    rw [s0id]
    exact s0rhs
  have s1id : 2*z*(B-u*M) = x*((t-1)*y*z+2*t*z-y-1)+2*z*(t+1) := by
    dsimp [B,M,D]; rw [←eu]; ring
  have s1rhs : 0 ≤ x*((t-1)*y*z+2*t*z-y-1)+2*z*(t+1) := by
    have hp := mul_nonneg ht0 hz0
    have hb : 0 ≤ (t-1)*y*z+2*t*z-y-1 := by nlinarith only [hc,hp]
    positivity
  have s1 : 0 ≤ B-u*M := by
    apply (mul_nonneg_iff_of_pos_left (by omega : 0 < 2*z)).mp
    rw [s1id]
    exact s1rhs
  have s2id : 2*y*(L-v*M) = x*((t-1)*y*z-y-1)+2*y*(t*z+z+1) := by
    dsimp [L,M,D]; rw [←ev]; ring
  have s2rhs : 0 ≤ x*((t-1)*y*z-y-1)+2*y*(t*z+z+1) := by positivity
  have s2 : 0 ≤ L-v*M := by
    apply (mul_nonneg_iff_of_pos_left (by omega : 0 < 2*y)).mp
    rw [s2id]
    exact s2rhs
  have t0id : 2*(3*h)*J-3*A-1 = 6*h*(y*(z-2*t)+y-2*t+1)-4 := by
    dsimp [J,M,A,D]; rw [←ex]; ring
  have t0 : 0 ≤ 2*(3*h)*J-3*A-1 := by
    have hp := mul_nonneg hy0 (by omega : 0 ≤ z-2*t)
    have hb : 1 ≤ y*(z-2*t)+y-2*t+1 := by omega
    have hm := mul_nonneg (by omega : 0 ≤ h-1) (by omega : 0 ≤ y*(z-2*t)+y-2*t+1)
    nlinarith only [t0id,hb,hm]
  have t1id : 2*z*(u*J-B) = x*z*(y-2*t)+2*(t+1)*(y-z)+y*(x-2*t-2)+x := by
    dsimp [J,M,B,D]; rw [←eu]; ring
  have t1rhs : 0 ≤ x*z*(y-2*t)+2*(t+1)*(y-z)+y*(x-2*t-2)+x := by
    have h1 : 0 ≤ y-2*t := by omega
    have h2 : 0 ≤ y-z := by omega
    have h3 : 0 ≤ x-2*t-2 := by omega
    positivity
  have t1 : 0 ≤ u*J-B := by
    apply (mul_nonneg_iff_of_pos_left (by omega : 0 < 2*z)).mp
    rw [t1id]
    exact t1rhs
  have t2id : 2*y*(2*v*J-(2*L-1-z)-1) =
      2*(y*z*(x-2*t-1)+y*(x-2)+x) := by
    dsimp [J,M,L,D]; rw [←ev]; ring
  have t2rhs : 0 ≤ 2*(y*z*(x-2*t-1)+y*(x-2)+x) := by
    have h1 : 0 ≤ x-2*t-1 := by omega
    have h2 : 0 ≤ x-2 := by omega
    positivity
  have t2 : 0 ≤ 2*v*J-(2*L-1-z)-1 := by
    apply (mul_nonneg_iff_of_pos_left (by omega : 0 < 2*y)).mp
    rw [t2id]
    exact t2rhs
  have hD : z+2 ≤ D := by dsimp [D]; nlinarith only [mul_nonneg (by omega : 0 ≤ y-1) hz0, show 1 ≤ y by omega]
  have huD : D ≤ u*D := by nlinarith only [mul_nonneg (by omega : 0 ≤ u-1) (by omega : 0 ≤ D)]
  have hvD : D ≤ v*D := by nlinarith only [mul_nonneg (by omega : 0 ≤ v-1) (by omega : 0 ≤ D)]
  have hhD : 0 ≤ 3*h*D := by positivity
  have hA : 1 ≤ A := by dsimp [A]; nlinarith only [mul_nonneg hx0 (by omega : 0 ≤ D)]
  refine ⟨s0,s1,s2,t0,t1,t2,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp [J] at *
  · nlinarith only [s0,hhD]
  · nlinarith only [s1,huD,hD,hz0]
  · nlinarith only [s2,hvD,hD]
  · nlinarith only [t0,hhD,hA]
  · nlinarith only [t1,huD,hD,hz0]
  · nlinarith only [t2,hvD,hD,hz0]

end D5.S3.Combinatorics.Circle.FourNegative.Descending
