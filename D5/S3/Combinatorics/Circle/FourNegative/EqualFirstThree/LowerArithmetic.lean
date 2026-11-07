/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstThree/LowerArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-delayed-ear-bounds)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Delayed-ear strip inequalities in the complete lower small-d window. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Arithmetic

/-! These inequalities use the two actual ear modes rather than a strong shadow strip. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
open private seed eta vcoef wcoef xcoef
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree.Source
open private seed_bounds
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Source

private def Bounds (p q r n1 n2 n3 n4 B h : ℤ) : Prop :=
  2*h+2*p ≤ 2*B ∧ 0 ≤ 2*h+2*p+n1 ∧
  2*h+2*p+n1+2*q ≤ 2*B ∧ 0 ≤ 2*h+2*p+n1+2*q+n2 ∧
  2*h+2*p+n1+2*q+n2+2*r ≤ 2*B ∧
  0 ≤ 2*h+2*p+n1+2*q+n2+2*r+n3 ∧
  0 ≤ -n4 ∧ -n4 ≤ 2*B

set_option maxHeartbeats 1600000 in
private theorem lower_bounds (R D H r e B : ℤ)
    (hD : 4 ≤ D) (hH : 2 ≤ H) (hHD : 2*H ≤ D)
    (hRH : D*H=R) (hr : 2*r=R) (he : 2*e=D)
    (hB : 2*B=D*R*R*R-2) :
    let A := seed R
    let C := eta R
    let V := vcoef R D
    let W := wcoef R D
    let X := xcoef R D
    let N := D*R*R*R-1
    let n := H-1
    Bounds ((r-1)*V) ((r-1)*W) ((e-1)*A+n*X)
      (W-N) (X-N) (V-N) (A-N) B 0 ∧
    Bounds ((r-1)*(2*V-1)) ((r-1)*(2*W-R-1))
      ((e-1)*(2*A)+n*(2*X-C))
      (2*W-R-1-(2*N+1)) (2*X-C-(2*N+1))
      (2*V-1-(2*N+1)) (A-(2*N+1)) N 0 := by
  dsimp only
  let A := seed R
  let C := eta R
  let V := vcoef R D
  let W := wcoef R D
  let X := xcoef R D
  let N := D*R*R*R-1
  let n := H-1
  let p := (r-1)*V
  let q := (r-1)*W
  let t := (e-1)*A+n*X
  let pn := (r-1)*(2*V-1)
  let qn := (r-1)*(2*W-R-1)
  let tn := (e-1)*(2*A)+n*(2*X-C)
  have hR : 4 ≤ R := by nlinarith
  have hRD : 2*D ≤ R := by nlinarith only [hD,hH,hRH]
  have hn : 0 ≤ n := by dsimp [n]; omega
  have hr1 : 1 ≤ r := by omega
  have hC : 0 ≤ C := by dsimp [C,eta]; positivity
  have hA : 1 ≤ A ∧ A < N := by
    have h := seed_bounds R R R D hR hR hR hD
    change 1 ≤ A ∧ A < R*R*R*D-1 at h
    have hh : R*R*R*D-1=N := by dsimp [N]; ring
    rw [hh] at h; exact h
  have hRV : R*V=N+W := by dsimp [V,N,W,vcoef,wcoef]; ring
  have hRW : R*W=N+X := by dsimp [W,N,X,wcoef,xcoef]; ring
  have hDA : D*A=N+V := by dsimp [A,N,V,seed,vcoef]; ring
  have hWV : W-V=R-D := by dsimp [W,V,wcoef,vcoef]; ring
  have hXV : X-V=(R-D)*(R+1) := by dsimp [X,V,xcoef,vcoef]; ring
  have hHX : H*X=A+n*C := by
    dsimp [X,A,n,C,xcoef,seed,eta]
    linear_combination (R*R)*hRH
  have hp : 2*p=N+W-2*V := by dsimp only [p]; linear_combination V*hr+hRV
  have hq : 2*q=N+X-2*W := by dsimp only [q]; linear_combination W*hr+hRW
  have ht : 2*t=N+V-2*A+2*n*X := by dsimp only [t]; linear_combination A*he+hDA
  have hnX : n*X=H*X-X := by dsimp [n]; ring
  have hseam1 : 2*p+(W-N)=2*(R-D) := by omega
  have hseam2 : 2*p+(W-N)+2*q+(X-N)=2*(R-D)*(R+1) := by nlinarith only [hp,hq,hXV]
  have hseam3 : 2*p+(W-N)+2*q+(X-N)+2*t+(V-N)=2*n*C := by
    nlinarith only [hp,hq,ht,hHX,hnX]
  have hDm : 0≤D-1 := by omega
  have hDmm : 0≤2*D-1 := by omega
  have hRDm : 0≤R-D := by omega
  have hRDmm : 0≤R-2*D := by omega
  have hWVbound : W ≤ 2*V-1 := by
    have hh : 0 ≤ D*R*R+(D-1)*R+2*D := by positivity
    dsimp [W,V,wcoef,vcoef]
    nlinarith only [hh]
  have hXVbound : X ≤ 2*V-1 := by
    have hh : 0 ≤ (D-1)*R*R+(2*D-1)*R+2*D := by positivity
    dsimp [X,V,xcoef,vcoef]
    nlinarith only [hh]
  have hcharge : 2*n*C ≤ V-1 := by
    have hnD : 2*n ≤ D := by dsimp [n]; omega
    have hh := mul_le_mul_of_nonneg_right hnD hC
    have hVC : V-1=D*C := by dsimp [V,C,vcoef,eta]; ring
    nlinarith only [hh,hVC]
  have hseam10 : 0 ≤ 2*(R-D) := by omega
  have hseam20 : 0 ≤ 2*(R-D)*(R+1) := by positivity
  have hseam30 : 0 ≤ 2*n*C := by positivity
  have hN : 2*B=N-1 := by dsimp [N]; omega
  have ho1 : 2*p ≤ 2*B := by omega
  have ho2 : 2*p+(W-N)+2*q ≤ 2*B := by omega
  have ho3 : 2*p+(W-N)+2*q+(X-N)+2*t ≤ 2*B := by omega
  have hold : Bounds p q t (W-N) (X-N) (V-N) (A-N) B 0 := by
    dsimp only [Bounds]
    refine ⟨by omega,by omega,by omega,by omega,by omega,by omega,by omega,by omega⟩
  have hpn : 2*pn=4*p-2*(r-1) := by dsimp [pn,p]; ring
  have hqn : 2*pn+(2*W-R-1-(2*N+1))+2*qn =
      2*(2*p+(W-N)+2*q)-2*R-2*(r-1)*(R+1) := by
    dsimp only [pn,qn,p,q]
    linear_combination -hr
  have htn : 2*pn+(2*W-R-1-(2*N+1))+2*qn+
      (2*X-C-(2*N+1))+2*tn =
      2*(2*p+(W-N)+2*q+(X-N)+2*t)-2*(R+R*R)-2*n*C := by
    dsimp only [pn,qn,tn,p,q,t]
    dsimp [C,eta]
    linear_combination -(R+2)*hr
  have hnew1 : 2*pn+(2*W-R-1-(2*N+1))=2*(R-2*D) := by
    nlinarith only [hpn,hseam1,hr]
  have hnew2 : 2*pn+(2*W-R-1-(2*N+1))+2*qn+
      (2*X-C-(2*N+1))=2*(R-2*D)*(R+1) := by
    dsimp [C,eta] at hqn ⊢
    have heq : 2*(r-1)*(R+1)=(R-2)*(R+1) := by linear_combination (R+1)*hr
    nlinarith only [hqn,hseam2,heq]
  have hnew3 : 2*pn+(2*W-R-1-(2*N+1))+2*qn+
      (2*X-C-(2*N+1))+2*tn+(2*V-1-(2*N+1))=2*(H-2)*C := by
    have hnC : n*C=(H-1)*C := rfl
    have hVC : V-1=D*C := by dsimp [V,C,vcoef,eta]; ring
    have hHXn : H*(2*X-C)-2*A=(H-2)*C := by
      dsimp [n] at hHX
      nlinarith only [hHX]
    have huNew : 2*(e-1)*(2*A)+(2*V-1-(2*N+1))=2*(2*V-1-2*A) := by
      linear_combination (2*A)*he+2*hDA
    have hvNew : 2*pn+(2*W-R-1-(2*N+1))=2*(2*W-R-1-(2*V-1)) := by
      dsimp [pn]
      linear_combination (2*V-1)*hr+2*hRV
    have hwNew : 2*qn+(2*X-C-(2*N+1))=2*(2*X-C-(2*W-R-1)) := by
      dsimp [qn,C,eta]
      linear_combination (2*W-R-1)*hr+2*hRW
    have hnn : n*(2*X-C)=H*(2*X-C)-(2*X-C) := by dsimp [n]; ring
    dsimp only [tn]
    nlinarith only [huNew,hvNew,hwNew,hHXn,hnn]
  have hnp : 0 ≤ 2*(r-1) := by omega
  have hnq : 0 ≤ 2*R+2*(r-1)*(R+1) := by positivity
  have hnt : 0 ≤ 2*(R+R*R)+2*n*C := by positivity
  have hnew10 : 0 ≤ 2*(R-2*D) := by omega
  have hnew20 : 0 ≤ 2*(R-2*D)*(R+1) := by positivity
  have hnew30 : 0 ≤ 2*(H-2)*C := by positivity
  refine ⟨hold,?_⟩
  change Bounds pn qn tn _ _ _ _ N 0
  dsimp only [Bounds]
  refine ⟨?_,by omega,?_,by omega,?_,by omega,by omega,by omega⟩ <;>
    nlinarith only [hpn,hqn,htn,ho1,ho2,ho3,hN,hnp,hnq,hnt]

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstThree
