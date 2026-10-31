/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/HardArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-last-u-bounds)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Exact two-mode bounds for the last-U floor schedule. -/
import Mathlib.Data.Int.DivMod
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open private seed eta vcoef wcoef xcoef
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private Bounds from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.LowerArithmetic
open private seed_bounds from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

-- Packet identities and the floor remainder are checked together over unbounded integers.
set_option maxHeartbeats 2000000 in
private theorem hard_bounds (R D H r e B HU x L : ℤ)
    (hD : 4 ≤ D) (hH : 2 ≤ H) (hRD : 2*D ≤ R)
    (hRH : D*H=R) (hr : 2*r=R) (he : 2*e=D)
    (hB : 2*B=D*R*R*R-2)
    (hHU : 2*HU=D*R*R*R-1-vcoef R D)
    (hL : 2*L=seed R-1)
    (hx0 : 0≤x)
    (hfloor : 0 ≤ HU-(r-H)*wcoef R D-x*xcoef R D ∧
      1 ≤ 2*(HU-(r-H)*wcoef R D-x*xcoef R D)+1+(R+1)*(r-H)+eta R*x ∧
      2*(HU-(r-H)*wcoef R D-x*xcoef R D)+1+(R+1)*(r-H)+eta R*x ≤ L) :
    let A := seed R
    let C := eta R
    let V := vcoef R D
    let W := wcoef R D
    let X := xcoef R D
    let N := D*R*R*R-1
    let n := H-1
    let p := (e-1)*A+n*V
    let q := (r-H)*V+n*W
    let t := (r-1-x)*X
    Bounds p q t (X-N) (W-N) (A-N) (V-N) B 0 ∧
    Bounds ((e-1)*(2*A)+n*(2*V-1))
      ((r-H)*(2*V-1)+n*(2*W-R-1)) ((r-1-x)*(2*X-C)+A)
      (2*X-C-(2*N+1)) (2*W-R-1-(2*N+1))
      (A-(2*N+1)) (2*V-1-(2*N+1)) N 0 := by
  dsimp only
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := D*R*R*R-1
  let n := H-1
  let p := (e-1)*A+n*V
  let q := (r-H)*V+n*W
  let t := (r-1-x)*X
  let pn := (e-1)*(2*A)+n*(2*V-1)
  let qn := (r-H)*(2*V-1)+n*(2*W-R-1)
  let tn := (r-1-x)*(2*X-C)+A
  let S := HU-(r-H)*W-x*X
  let Q := 1+(R+1)*(r-H)+C*x
  let E := 2*S+Q
  have hR : 4≤R := by omega
  have hn : 0≤n := by dsimp [n];omega
  have hnOne : 1≤n := by dsimp [n];omega
  have hw : 0≤r-H := by nlinarith only [hD,hRH,hr,hH]
  have hC0 : 0≤C := by dsimp [C,eta];positivity
  have hRD0 : 0≤R-D := by omega
  have hRD20 : 0≤R-2*D := by omega
  have hDm : 0≤D-1 := by omega
  have hRR : 0≤R*R := mul_self_nonneg R
  have hA : 1≤A ∧ A<N := by
    have h := seed_bounds R R R D hR hR hR hD
    change 1≤A ∧ A<R*R*R*D-1 at h
    have hh : R*R*R*D-1=N := by dsimp [N];ring
    rwa [hh] at h
  have hV : 1≤V ∧ V<N := by
    constructor
    · have hv : 0<V := by dsimp [V,vcoef];positivity
      omega
    · apply Int.lt_iff_add_one_le.mpr
      apply sub_nonneg.mp
      let z := R-4
      let t0 := D-4
      have hz : 0≤z := by dsimp [z];omega
      have ht0 : 0≤t0 := by dsimp [t0];omega
      have erz : R=z+4 := by dsimp [z];ring
      have edt : D=t0+4 := by dsimp [t0];ring
      dsimp [V,N,vcoef]
      rw [erz,edt]
      ring_nf
      positivity
  have hN : 2*B=N-1 := by dsimp [N];omega
  have hS : 0≤S := hfloor.1
  have hE : 1≤E ∧ E≤L := by
    dsimp only [E,Q]
    have h1 := hfloor.2.1
    have h2 := hfloor.2.2
    change 1≤2*S+1+(R+1)*(r-H)+C*x at h1
    change 2*S+1+(R+1)*(r-H)+C*x≤L at h2
    constructor <;> omega
  have hDA : D*A=N+V := by dsimp [A,N,V,seed,vcoef];ring
  have hRV : R*V=N+W := by dsimp [V,N,W,vcoef,wcoef];ring
  have hRW : R*W=N+X := by dsimp [W,N,X,wcoef,xcoef];ring
  have hRX : R*X=N+A := by dsimp [X,N,A,xcoef,seed];ring
  have hs1 : 2*p+(X-N)=(R-D)*(R+1)+2*n := by
    dsimp [p,n,A,V,X,N,seed,vcoef,xcoef]
    linear_combination (norm := (try dsimp [A,C,V,W,X,N,n,p,q,t,pn,qn,tn,S,Q,E,seed,eta,vcoef,wcoef,xcoef]; ring)) 2*(R*R+R+1)*hRH+(seed R)*he
  have hs2 : 2*p+(X-N)+2*q+(W-N)=(D+2)*n*(R+1) := by
    dsimp [p,q,n,A,V,W,X,N,seed,vcoef,wcoef,xcoef]
    linear_combination (norm := (try dsimp [A,C,V,W,X,N,n,p,q,t,pn,qn,tn,S,Q,E,seed,eta,vcoef,wcoef,xcoef]; ring)) (seed R)*he+(vcoef R D)*hr+(2*R-1)*(R+1)*hRH
  have hs3 : 2*p+(X-N)+2*q+(W-N)+2*t+(A-N)=2*S := by
    dsimp only [p,q,t,S,n]
    linear_combination (norm := (try dsimp [A,C,V,W,X,N,n,p,q,t,pn,qn,tn,S,Q,E,seed,eta,vcoef,wcoef,xcoef]; ring)) A*he+V*hr+W*hr+X*hr+hDA+hRV+hRW+hRX-hHU
  have hp1 : 2*p≤N-1 := by
    have hcap : 2*n≤D*C := by
      have hHC : 2*H≤D*H := by nlinarith only [hD,hH]
      have hRC : R≤D*C := by
        dsimp [C,eta]
        have hrr : 0≤D*R*R+(D-1)*R+D := by positivity
        nlinarith only [hrr]
      dsimp [n];omega
    have heq : X-1-((R-D)*(R+1)+2*n)=D*C-2*n := by dsimp [X,C,xcoef,eta];ring
    omega
  have hp2 : 2*p+(X-N)+2*q≤N-1 := by
    have hcap : (D+2)*n≤D*R := by
      have hDD : D+2≤D*D := by nlinarith
      have hh := mul_le_mul_of_nonneg_right hDD (show 0≤H by omega)
      have hre : D*D*H=D*R := by
        calc
          D*D*H = D*(D*H) := by ring
          _ = D*R := by rw [hRH]
      dsimp [n];nlinarith only [hh,hre,hD]
    have hh := mul_le_mul_of_nonneg_right hcap (show 0≤R+1 by omega)
    have heq : W-1=D*R*(R+1)+R := by dsimp [W,wcoef];ring
    omega
  have hq0 : 0≤Q := by
    dsimp [Q,C,eta];positivity
  have hp3 : 2*p+(X-N)+2*q+(W-N)+2*t≤N-1 := by omega
  have hseam10 : 0≤(R-D)*(R+1)+2*n := by positivity
  have hseam20 : 0≤(D+2)*n*(R+1) := by positivity
  have hpn : 2*pn=4*p-2*n := by dsimp [pn,p];ring
  have hn1 : 2*pn+(2*X-C-(2*N+1))=(R-2*D)*(R+1)+2*n-2 := by
    dsimp [C,eta]
    nlinarith only [hs1,hpn]
  have hn2 : 2*pn+(2*X-C-(2*N+1))+2*qn+(2*W-R-1-(2*N+1))=
      ((R-2*D)*(R+1)+2*n-2)+2*H*(R-2*D) := by
    dsimp only [qn,pn,p,q,n]
    dsimp [C,eta]
    linear_combination (norm := (try dsimp [A,C,V,W,X,N,n,p,q,t,pn,qn,tn,S,Q,E,seed,eta,vcoef,wcoef,xcoef]; ring)) 2*(seed R)*he+(2*vcoef R D-1)*hr+4*(eta R)*hRH
  have hpeak2 : 2*pn+(2*X-C-(2*N+1))+2*qn =
      2*(2*p+(X-N)+2*q)-(C+1+2*n+2*((r-H)+(R+1)*n)) := by
    dsimp [pn,qn,p,q];ring
  have hpeak3 : 2*pn+(2*X-C-(2*N+1))+2*qn+(2*W-R-1-(2*N+1))+2*tn =
      2*E+2*N-2*L := by
    dsimp only [pn,qn,tn,E,Q,n]
    dsimp [C,eta,A,seed]
    linear_combination (norm := (try dsimp [A,C,V,W,X,N,n,p,q,t,pn,qn,tn,S,Q,E,seed,eta,vcoef,wcoef,xcoef]; ring)) 2*hs3-(eta R+R+2)*hr+hL
  have hnew1 : 0≤(R-2*D)*(R+1)+2*n-2 := by
    have hh : 0≤(R-2*D)*(R+1) := by positivity
    omega
  have hnew2 : 0≤2*H*(R-2*D) := by positivity
  have hcharge : 0≤C+1+2*n+2*((r-H)+(R+1)*n) := by dsimp [C,eta];positivity
  constructor
  · change Bounds p q t (X-N) (W-N) (A-N) (V-N) B 0
    dsimp only [Bounds]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
  · change Bounds pn qn tn _ _ _ _ N 0
    dsimp only [Bounds]
    exact ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
