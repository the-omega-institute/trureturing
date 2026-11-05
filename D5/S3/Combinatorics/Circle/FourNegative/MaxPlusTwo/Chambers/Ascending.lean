/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Ascending
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Ascending
   mirror-E: none(waiver:consumed-chamber-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Rounded reserve release and ascending first-stage inequalities. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

/-! Releasing a low U submask places the last reserve in its required interval. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private ceilpos ceilpos_bounds ceilpos_capacity mass_margin
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic

private theorem released_reserve (A E S : ℤ) (hA : 0<A) (hE : 2*A≤E)
    (hS : E≤S) (hcap : S≤2*E+2*A) :
    let ell:=ceilpos (S-2*E+A) A
    ell≤3 ∧ E≤S-A*ell ∧ S-A*ell≤2*E-A := by
  dsimp only
  have hc:=ceilpos_capacity (S-2*E+A) A 3 hA (by norm_num; linarith only [hcap])
  have hb:=ceilpos_bounds (S-2*E+A) A hA
  refine ⟨hc,?_,by linarith only [hb.1]⟩
  by_cases he : ceilpos (S-2*E+A) A=0
  · rw [he,Nat.cast_zero,mul_zero,sub_zero]
    exact hS
  · have hp : 0<ceilpos (S-2*E+A) A := by omega
    linarith only [hb.2 hp,hE]

private theorem ascending_first_bounds (R T Z : ℤ)
    (hR : 4≤R) (hT : 4≤T) (hZ : 4≤Z) (hZT : T≤Z) (hZR : 2*R≤Z) :
    let C:=R*T+R+1; let A:=R*T*Z+C
    let e1:=2*Z*C; let e3:=2*T*Z^2
    2*A<e1 ∧ e1≤3*A ∧ 3*A≤2*e1-A ∧ 2*A<e3 := by
  let C:=R*T+R+1
  let A:=R*T*Z+C
  let e1:=2*Z*C
  let e3:=2*T*Z^2
  have hm:=mass_margin R T Z hR hT hZ
  have hC : 0<C := by dsimp [C]; positivity
  have hRC : 0<Z*(R+1)-C := by
    have h:=mul_nonneg (show 0≤R by omega) (show 0≤Z-T by omega)
    dsimp [C]; nlinarith only [h,hZR,hR]
  have hfirst : 2*A<e1 := by dsimp [A,e1]; nlinarith only [hRC]
  have hcoef : 0≤R*T-2*R-2 := by
    have h:=mul_nonneg (show 0≤R by omega) (show 0≤T-4 by omega)
    nlinarith only [h,hR]
  have h3 : e1≤3*A := by
    have h:=mul_nonneg (show 0≤Z by omega) hcoef
    dsimp [e1,A,C] at *
    nlinarith only [h,hC]
  have hthird : 2*A<e3 := by
    have h:=mul_nonneg (show 0≤T*Z by positivity) (show 0≤Z-2*R by omega)
    dsimp [e3,A,C] at *
    nlinarith only [h,hm,hC]
  exact ⟨hfirst,h3,by linarith only [hfirst],hthird⟩

private theorem ascending_equal_end_V (R T : ℤ) (hR : 4≤R) (hT : 2*R≤T) :
    let Z:=T; let C:=R*T+R+1; let A:=R*T*Z+C
    let e1:=2*Z*C; let e2:=2*(R+1)*Z^2
    e1≤e2 ∧ e2≤3*A := by
  have h:=mul_nonneg (show 0≤T by omega) (show 0≤T-R-1 by omega)
  have h' :=mul_nonneg (show 0≤T^2 by positivity) (show 0≤R-2 by omega)
  dsimp only
  constructor <;> nlinarith only [h,h',hR,hT]

private theorem ascending_wide_V (R T Z : ℤ)
    (hR : 4≤R) (hT : 4≤T) (hZT : 2*T≤Z) (hZR : 4*R≤Z) :
    let C:=R*T+R+1
    2*(2*Z*C)≤2*(R+1)*Z^2 := by
  have h:=mul_nonneg (show 0≤R by omega) (show 0≤Z-2*T by omega)
  have hm : 0≤(R+1)*Z-2*(R*T+R+1) := by nlinarith only [h,hZR,hR]
  have hz : 0≤Z := by omega
  have hp:=mul_nonneg hz hm
  dsimp only
  nlinarith only [hp]

set_option maxHeartbeats 1000000 in
-- The adjacent T=R, Z=2R V-stage has rounded mask exactly one.
private theorem ascending_adjacent_V (R : ℤ) (hR : 4≤R) :
    let C:=R^2+R+1; let A:=2*R^3+C
    let e1:=4*R*C; let e2:=8*(R+1)*R^2
    0<e2-3*A ∧ e2-3*A≤2*e1 ∧
      e2≤3*A+2*e1 ∧ 3*A+2*e1≤2*e2-A := by
  have hr : 0≤R-4 := by omega
  generalize hr0 : R-4=r at hr
  have heR : R=r+4 := by omega
  dsimp only
  rw [heR]
  refine ⟨?_,?_,?_,?_⟩
  all_goals first | apply sub_nonneg.mp | apply sub_pos.mp
  all_goals ring_nf; positivity


set_option maxHeartbeats 1000000 in
-- The large adjacent-ratio chart bounds the amount of U release by three units.
private theorem ascending_double_release_cap (R Z : ℤ) (hR : 8≤R) (hZ : 4*R≤Z) :
    let C:=2*R^2+R+1; let A:=2*R^2*Z+C
    let e1:=2*Z*C; let e2:=2*(R+1)*Z^2; let e3:=4*R*Z^2
    e2+2*e1≤2*e3-2*e2+2*A := by
  have hr : 0≤R-8 := by omega
  have hz : 0≤Z-4*R := by omega
  generalize hr0 : R-8=r at hr
  generalize hz0 : Z-4*R=z at hz
  have heR : R=r+8 := by omega
  have heZ : Z=4*R+z := by omega
  dsimp only
  rw [heZ,heR]
  apply sub_nonneg.mp
  ring_nf; positivity

set_option maxHeartbeats 1000000 in
-- The smallest first gap has a separate unbounded Z chart.
private theorem ascending_four_release_cap (Z : ℤ) (hZ : 64≤Z) :
    let A:=32*Z+37
    let e1:=74*Z; let e2:=10*Z^2; let e3:=16*Z^2
    e2+2*e1≤2*e3-2*e2+2*A := by
  have hz : 0≤Z-64 := by omega
  generalize hz0 : Z-64=z at hz
  have heZ : Z=z+64 := by omega
  dsimp only
  rw [heZ]
  apply sub_nonneg.mp
  ring_nf; positivity

set_option maxHeartbeats 1000000 in
-- At T=R the last V reserve can be reduced using only the low U mask.
private theorem ascending_equal_release_cap (R Z : ℤ) (hR : 4≤R) (hZ : 2*R≤Z) :
    let C:=R^2+R+1; let A:=R^2*Z+C
    let e1:=2*Z*C; let e2:=2*(R+1)*Z^2; let e3:=2*R*Z^2
    e2+2*e1≤2*e3+2*A := by
  have hr : 0≤R-4 := by omega
  have hz : 0≤Z-2*R := by omega
  generalize hr0 : R-4=r at hr
  generalize hz0 : Z-2*R=z at hz
  have heR : R=r+4 := by omega
  have heZ : Z=2*R+z := by omega
  dsimp only
  rw [heZ,heR]
  apply sub_nonneg.mp
  ring_nf; positivity

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
