/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/LargeArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-large-d-bounds)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact first-ear strip bounds for every d at least s plus two. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic

/-! A single reserved physical U bit makes the entire large-d cone uniform. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open private seed eta vcoef wcoef xcoef
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private seed_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source
open private Bounds
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic

set_option maxHeartbeats 2000000 in
private theorem large_bounds (R D u r e B : ℤ)
    (hR : 4≤R) (hu : 2≤u) (hD : D=2*R*u)
    (hr : 2*r=R) (he : 2*e=D) (hB : 2*B=D*R*R*R-2) :
    let A := seed R
    let C := eta R
    let V := vcoef R D
    let W := wcoef R D
    let X := xcoef R D
    let N := D*R*R*R-1
    let p := (e-1-u)*A
    let q := (r-1)*V
    let t := (r-1)*W
    Bounds p q t (X-N) (W-N) (V-N) (A-N) B 0 ∧
    Bounds ((e-1-u)*(2*A)) ((r-1)*(2*V-1)) ((r-1)*(2*W-R-1))
      (2*X-C-(2*N+1)) (2*W-R-1-(2*N+1))
      (2*V-1-(2*N+1)) (A-(2*N+1)) N A := by
  dsimp only
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := D*R*R*R-1
  let p := (e-1-u)*A
  let q := (r-1)*V
  let t := (r-1)*W
  let pn := (e-1-u)*(2*A)
  let qn := (r-1)*(2*V-1)
  let tn := (r-1)*(2*W-R-1)
  let K := u*R^4
  let Z := (u-1)*R^3-u*C
  let Zn := 2*Z+R^3
  have heq : e=R*u := by nlinarith only [hD,he]
  have hD4 : 4≤D := by nlinarith
  have hA : 1≤A ∧ A<N := by
    have h := seed_bounds R R R D hR hR hR hD4
    change 1≤A ∧ A<R*R*R*D-1 at h
    have hh : R*R*R*D-1=N := by dsimp [N];ring
    rw [hh] at h;exact h
  have hC : 0≤C := by dsimp [C,eta];positivity
  have hbase : 0≤R^3-2*C := by
    let a := R-4
    have ha : 0≤a := by dsimp [a];omega
    have hh : 0≤a^3+10*a^2+30*a+22 := by positivity
    convert hh using 1 <;> dsimp [a,C,eta] <;> ring
  have hZm : 0≤Z := by
    have hbig : 0≤(u-2)*(R^3-C) := by
      have h1 : 0≤u-2 := by omega
      have h2 : 0≤R^3-C := by omega
      exact mul_nonneg h1 h2
    have hz : Z=(u-2)*(R^3-C)+(R^3-2*C) := by dsimp [Z];ring
    omega
  have hZnm : 0≤Zn := by dsimp [Zn];positivity
  have hplus : 0≤R*R+R := by positivity
  have hminus : 0≤R*R-R := by nlinarith
  have hu2m : 0≤2*u-1 := by omega
  have hu4m : 0≤4*u-1 := by omega
  have hmul1 : 0≤(2*u-1)*(R*R+R) := by positivity
  have hmul2 : 0≤(2*u-1)*(R*R-R) := by positivity
  have hmul3 : 0≤(4*u-1)*(R*R+R) := by positivity
  have hmul4 : 0≤(4*u-1)*(R*R-R) := by positivity
  have hN : N=2*K-1 := by dsimp [N,K];rw [hD];ring
  have hBB : B=K-1 := by omega
  have hp : p=K-u-A := by dsimp [p,K,A,seed];rw [heq];ring
  have hq : 2*q=(R-2)*V := by dsimp only [q];linear_combination V*hr
  have ht : 2*t=(R-2)*W := by dsimp only [t];linear_combination W*hr
  have hpn : pn=2*p := by dsimp [pn,p];ring
  have hqn : 2*qn=(R-2)*(2*V-1) := by dsimp only [qn];linear_combination (2*V-1)*hr
  have htn : 2*tn=(R-2)*(2*W-R-1) := by dsimp only [tn];linear_combination (2*W-R-1)*hr
  have hs1 : 2*p+(X-N)=2*Z+(2*u-1)*(R*R+R) := by
    rw [hp,hN];dsimp [X,Z,K,C,A,xcoef,eta,seed];rw [hD];ring
  have hs2 : 2*p+(X-N)+2*q+(W-N)=2*Z+(2*u-1)*(R*R-R) := by
    rw [hp,hq,hN];dsimp [X,W,V,Z,K,C,A,xcoef,wcoef,vcoef,eta,seed];rw [hD];ring
  have hs3 : 2*p+(X-N)+2*q+(W-N)+2*t+(V-N)=2*Z := by
    rw [hp,hq,ht,hN];dsimp [X,W,V,Z,K,C,A,xcoef,wcoef,vcoef,eta,seed];rw [hD];ring
  have hk2 : 2*p+(X-N)+2*q =
      2*K-2*u*(R+1)^2-(2*R^3+R^2+2) := by
    rw [hp,hq,hN];dsimp [X,V,K,A,xcoef,vcoef,seed];rw [hD];ring
  have hk3 : 2*p+(X-N)+2*q+(W-N)+2*t =
      2*K-2*u*(2*R^2+2*R+1)-2*R^3-2 := by
    rw [hp,hq,ht,hN];dsimp [X,W,V,K,A,xcoef,wcoef,vcoef,seed];rw [hD];ring
  have hn1 : 2*A+2*pn+(2*X-C-(2*N+1)) =
      2*Zn+(4*u-1)*(R*R+R) := by
    rw [hpn,hp,hN];dsimp [X,Zn,Z,K,C,A,xcoef,eta,seed];rw [hD];ring
  have hn2 : 2*A+2*pn+(2*X-C-(2*N+1))+2*qn+
      (2*W-R-1-(2*N+1))=2*Zn+(4*u-1)*(R*R-R) := by
    rw [hpn,hp,hqn,hN];dsimp [X,W,V,Zn,Z,K,C,A,xcoef,wcoef,vcoef,eta,seed];rw [hD];ring
  have hn3 : 2*A+2*pn+(2*X-C-(2*N+1))+2*qn+
      (2*W-R-1-(2*N+1))+2*tn+(2*V-1-(2*N+1))=2*Zn := by
    rw [hpn,hp,hqn,htn,hN];dsimp [X,W,V,Zn,Z,K,C,A,xcoef,wcoef,vcoef,eta,seed];rw [hD];ring
  have hnk2 : 2*A+2*pn+(2*X-C-(2*N+1))+2*qn =
      4*K-4*u*(R+1)^2-(2*R^3+R^2+2) := by
    rw [hpn,hp,hqn,hN];dsimp [X,V,K,C,A,xcoef,vcoef,eta,seed];rw [hD];ring
  have hnk3 : 2*A+2*pn+(2*X-C-(2*N+1))+2*qn+
      (2*W-R-1-(2*N+1))+2*tn =
      4*K-4*u*(2*R^2+2*R+1)-2*R^3-2 := by
    rw [hpn,hp,hqn,htn,hN];dsimp [X,W,V,K,C,A,xcoef,wcoef,vcoef,eta,seed];rw [hD];ring
  have hp2 : 0≤2*u*(R+1)^2+2*R^3+R^2 := by positivity
  have hp3 : 0≤2*u*(2*R^2+2*R+1)+2*R^3 := by positivity
  have hnp2 : 0≤4*u*(R+1)^2+2*R^3+R^2 := by positivity
  have hnp3 : 0≤4*u*(2*R^2+2*R+1)+2*R^3 := by positivity
  constructor
  · change Bounds p q t (X-N) (W-N) (V-N) (A-N) B 0
    dsimp only [Bounds]
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
  · change Bounds pn qn tn _ _ _ _ N A
    dsimp only [Bounds]
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
