/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualOuter/StrictArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-unbounded-window-arithmetic)
   mirror-E: none(waiver:private-consumed-unbounded-window-arithmetic)
   anchors: [mathlib/module/Mathlib.Tactic.Ring]
   utility: none
   digest: W-X-U-V windows with all five strict payment branches. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

/-! W-X-U-V windows with all five strict payment branches. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
open private A B L H K SU SV SW
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter.Source

private theorem scalar_floor (u v : ℤ) (hv : 0<v) :
    0≤u-(u/v)*v ∧ u-(u/v)*v≤v-1 := by
  have h0:=Int.emod_nonneg u (ne_of_gt hv)
  have h1:=Int.emod_lt_of_pos u hv
  have he:=Int.ediv_mul_add_emod u v
  omega

set_option maxHeartbeats 2400000 in
private theorem strict_first_windows (x z r : ℤ) (hx : 4≤x) (hz : 2*x≤z) (hr : 1≤r) :
    let y:=4*x*r
    let s:=3*r
    (0≤2*(K x y z-s*L x z) ∧ 2*(K x y z-s*L x z)≤K x y z-1) ∧
    (0≤2*(SW x y z-s*SV x z) ∧ 2*(SW x y z-s*SV x z)≤SW x y z-1) ∧
    (0≤2*(A x y z-s*L x z) ∧ 2*(A x y z-s*L x z)≤A x y z-1) ∧
    (0≤2*(2*A x y z-s*SV x z) ∧ 2*(2*A x y z-s*SV x z)≤A x y z-1) := by
  let u:=x-4
  let w:=z-2*x
  let h:=r-1
  have hu : 0≤u := by dsimp [u]; omega
  have hw : 0≤w := by dsimp [w]; omega
  have hh : 0≤h := by dsimp [h]; omega
  have ex : x=u+4 := by dsimp [u]; ring
  have ez : z=2*(u+4)+w := by dsimp [u,w]; ring
  have er : r=h+1 := by dsimp [h]; ring
  dsimp only
  rw [ex,ez,er]
  have c0 : 0≤2*(K (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*L (u+4) (2*(u+4)+w)) := by
    dsimp [K,H,L]; ring_nf; positivity
  have c1 : 0≤K (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-1-
      2*(K (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*L (u+4) (2*(u+4)+w)) := by
    dsimp [K,H,L]; ring_nf; positivity
  have c2 : 0≤2*(SW (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*SV (u+4) (2*(u+4)+w)) := by
    dsimp [SW,K,H,SV,L]; ring_nf; positivity
  have c3 : 0≤SW (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-1-
      2*(SW (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*SV (u+4) (2*(u+4)+w)) := by
    dsimp [SW,K,H,SV,L]; ring_nf; positivity
  have c4 : 0≤2*(A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*L (u+4) (2*(u+4)+w)) := by
    dsimp [A,L]; ring_nf; positivity
  have c5 : 0≤A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-1-
      2*(A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*L (u+4) (2*(u+4)+w)) := by
    dsimp [A,L]; ring_nf; positivity
  have c6 : 0≤2*(2*A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*SV (u+4) (2*(u+4)+w)) := by
    dsimp [A,SV,L]; ring_nf; positivity
  have c7 : 0≤A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-1-
      2*(2*A (u+4) (4*(u+4)*(h+1)) (2*(u+4)+w)-3*(h+1)*SV (u+4) (2*(u+4)+w)) := by
    dsimp [A,SV,L]; ring_nf; positivity
  exact ⟨⟨c0,by linarith only [c1]⟩,⟨c2,by linarith only [c3]⟩,
    ⟨c4,by linarith only [c5]⟩,⟨c6,by linarith only [c7]⟩⟩

set_option maxHeartbeats 2400000 in
private theorem strict_payment (x z y v t : ℤ)
    (hx : 4≤x) (hz : 2*x≤z) (hv : 1≤v ∧ v≤4) (ht : 1≤t)
    (branch :
      (∃ p : ℤ, 2≤p ∧ z=2*x ∧ y=2*p*x ∧ v=2 ∧ 2*t=3*p) ∨
      (∃ p : ℤ, 4≤p ∧ y=p*z ∧ v=1 ∧ t=B x y/L x z) ∨
      (y=2*z ∧ v=2 ∧ t=3) ∨
      (x=4 ∧ z=16 ∧ y=32 ∧ v=4 ∧ t=6) ∨
      (8≤x ∧ y=2*z ∧ v=3 ∧ t=5)) :
    (0≤2*(v*B x y-t*L x z) ∧ 2*(v*B x y-t*L x z)≤B x y-1) ∧
    (0≤2*(v*SU x y-t*SV x z) ∧ 2*(v*SU x y-t*SV x z)≤SU x y-1) := by
  let G:=v*B x y-t*L x z
  let Gp:=v*SU x y-t*SV x z
  have hid : Gp=2*G-v+t*(z+1) := by dsimp [G,Gp,SU,SV]; ring
  have hz8 : 8≤z := by omega
  have hc : 0≤t*(z+1)-v := by nlinarith only [hv.2,ht,hz8]
  suffices hp : 0≤G ∧ Gp≤B x y-1 by
    have hU : SU x y=2*B x y-1 := rfl
    exact ⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩⟩
  rcases branch with h1|h2|h3|h4|h5
  · obtain ⟨p,hp,rfl,rfl,rfl,htp⟩:=h1
    let u:=x-4
    let w:=p-2
    have hu : 0≤u := by dsimp [u]; omega
    have hw : 0≤w := by dsimp [w]; omega
    have ex : x=u+4 := by dsimp [u]; ring
    have ep : p=w+2 := by dsimp [w]; ring
    have c0 : 0≤(x^2-3*x-3)*(2*p*x)+4*(x^2+x+1)-3*p := by
      rw [ex,ep]; ring_nf; positivity
    have c1 : 0≤3*p+(6*x+3)*(2*p*x)-6*(x^2+x+1)+2 := by
      rw [ex,ep]; ring_nf; positivity
    have hm : (2*t)*L x (2*x)=(3*p)*L x (2*x) := congrArg (fun n : ℤ => n*L x (2*x)) htp
    have hmV := congrArg (fun n : ℤ => n * SV x (2*x)) htp
    dsimp [G,Gp,B,L,SU,SV] at hm hmV ⊢
    constructor <;> nlinarith only [c0,c1,hm,hmV]
  · obtain ⟨p,hp,rfl,rfl,rfl⟩:=h2
    have hz0 : 0≤z := by omega
    have hx0 : 0≤x := by omega
    have hL : 0<L x z := by dsimp [L]; positivity
    have hf:=scalar_floor (B x (p*z)) (L x z) hL
    let u:=x-4
    let w:=z-2*x
    let h:=p-4
    have hu : 0≤u := by dsimp [u]; omega
    have hw : 0≤w := by dsimp [w]; omega
    have hh : 0≤h := by dsimp [h]; omega
    have ex : x=u+4 := by dsimp [u]; ring
    have ez : z=2*(u+4)+w := by dsimp [u,w]; ring
    have ep : p=h+4 := by dsimp [h]; ring
    have hC : 0<p*L x z-B x (p*z) := by
      have hP : 0<p*L x z-B x (p*z) := by
        rw [ex,ez,ep]; dsimp [L,B]; ring_nf; positivity
      exact hP
    have hpay : 0<B x (p*z)-2*L x z-p*(z+1) := by
      rw [ex,ez,ep]; dsimp [L,B]; ring_nf; positivity
    have htp : B x (p*z)/L x z<p := by
      by_contra hn
      have hm:=mul_le_mul_of_nonneg_right (show p≤B x (p*z)/L x z by omega) hL.le
      nlinarith only [hm,hf.1,hC]
    have hz1 : 0≤z+1 := by omega
    have hm:=mul_le_mul_of_nonneg_right (le_of_lt htp) hz1
    dsimp [G,Gp]
    rw [show SU x (p*z)=2*B x (p*z)-1 by rfl,
      show SV x z=2*L x z-1-z by rfl]
    constructor
    · simpa only [one_mul] using hf.1
    · nlinarith only [hf.2,hpay,hm]
  · obtain ⟨rfl,rfl,rfl⟩:=h3
    let u:=x-4
    let w:=z-2*x
    have hu : 0≤u := by dsimp [u]; omega
    have hw : 0≤w := by dsimp [w]; omega
    have ex : x=u+4 := by dsimp [u]; ring
    have ez : z=2*(u+4)+w := by dsimp [u,w]; ring
    have c0 : 0≤G := by dsimp [G,B,L]; rw [ex,ez]; ring_nf; positivity
    have c1 : 0≤B x (2*z)-1-Gp := by dsimp [Gp,B,L,SU,SV]; rw [ex,ez]; ring_nf; positivity
    exact ⟨c0,by linarith only [c1]⟩
  · obtain ⟨rfl,rfl,rfl,rfl,rfl⟩:=h4
    norm_num [G,Gp,B,L,SU,SV]
  · obtain ⟨hx8,rfl,rfl,rfl⟩:=h5
    let u:=x-8
    let w:=z-2*x
    have hu : 0≤u := by dsimp [u]; omega
    have hw : 0≤w := by dsimp [w]; omega
    have ex : x=u+8 := by dsimp [u]; ring
    have ez : z=2*(u+8)+w := by dsimp [u,w]; ring
    have c0 : 0≤G := by dsimp [G,B,L]; rw [ex,ez]; ring_nf; positivity
    have c1 : 0≤B x (2*z)-1-Gp := by dsimp [Gp,B,L,SU,SV]; rw [ex,ez]; ring_nf; positivity
    exact ⟨c0,by linarith only [c1]⟩

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualOuter
