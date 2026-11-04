/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Source
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Source
   mirror-E: none(waiver:internal-source-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual centered shadow and charge derived from the paired source table. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
import D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

/-! The charge is 2f-g and the shadow is g-f, both at actual physical labels. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open SourceWidth PeriodicShortening RunFirstEarTransport
open private source_table from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private negative_step from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift

private theorem two_power_pred (n : ℕ) (hn : 1 ≤ n) :
    (2:ℤ)^n = 2*2^(n-1) := by
  calc
    (2:ℤ)^n = 2^((n-1)+1) := by congr 1; omega
    _ = 2*2^(n-1) := by rw [pow_succ]; ring

set_option maxHeartbeats 1000000 in
/-- Charge and shadow are differences of the two actual centered sources. -/
private theorem source_shadow_charge (a b c d : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 3 ≤ d) :
    let R : ℤ := 2^a
    let T : ℤ := 2^b
    let Z : ℤ := 2^c
    let D : ℤ := 2^d
    let C := 1+R+R*T
    let A := R*T*Z+C
    let B := 2^(d-1)*R*T*Z
    let e1 := 2^(d-1)*C
    let e2 := 2^(d-1)*(R+1)*Z
    let e3 := 2^(d-1)*T*Z
    let Cp := T*Z+T+1
    let N := R*T*Z*D-1
    let f := fun i : ℕ => centered N ((2:ℤ)^i*A)
    let g := fun i : ℕ => centered (2*N+1) ((2:ℤ)^i*(2*A))
    let q := fun i => 2*f i-g i
    let z := fun i => g i-f i
    (∀ i<d, q i=(if i+1<d then 0 else 1) ∧
      z i=(if i+1<d then 2^i*A else -B+e1)) ∧
    (∀ i<c, q (d+i)=(if i+1<c then 2^i else 2^(c-1)+1) ∧
      z (d+i)=(if i+1<c then 2^i*(2*e1) else -B+e2)) ∧
    (∀ i<b, q (d+c+i)=(if i+1<b then 2^i*(Z+1) else 2^(b-1)*(Z+1)+1) ∧
      z (d+c+i)=(if i+1<b then 2^i*(2*e2) else -B+e3)) ∧
    (∀ i<a, q (d+c+b+i)=(if i+1<a then 2^i*Cp else 2^(a-1)*Cp+1) ∧
      z (d+c+b+i)=(if i+1<a then 2^i*(2*e3) else -B)) ∧
    g (d+c+b+a)=A := by
  dsimp only
  let R : ℤ := 2^a
  let T : ℤ := 2^b
  let Z : ℤ := 2^c
  let D : ℤ := 2^d
  let C := 1+R+R*T
  let A := R*T*Z+C
  let V := D*C+1
  let W := D*(Z*(1+R))+1+Z
  let X := D*(T*Z)+1+T+T*Z
  let N := R*T*Z*D-1
  let f := fun i : ℕ => centered N ((2:ℤ)^i*A)
  let g := fun i : ℕ => centered (2*N+1) ((2:ℤ)^i*(2*A))
  have hD : D=2*(2:ℤ)^(d-1) := two_power_pred d (by omega)
  have hR : R=2*(2:ℤ)^(a-1) := two_power_pred a (by omega)
  have hT : T=2*(2:ℤ)^(b-1) := two_power_pred b (by omega)
  have hZ : Z=2*(2:ℤ)^(c-1) := two_power_pred c (by omega)
  obtain ⟨_,_,_,_,uf,vf,wf,xf,ug,vg,wg,xg,fresh⟩ :=
    source_table a b c d ha hb hc (by omega)
  change ∀ i<d, f i=if i+1<d then 2^i*A else -(N-V)/2 at uf
  change ∀ i<c, f (d+i)=if i+1<c then 2^i*V else -(N-W)/2 at vf
  change ∀ i<b, f (d+c+i)=if i+1<b then 2^i*W else -(N-X)/2 at wf
  change ∀ i<a, f (d+c+b+i)=if i+1<a then 2^i*X else -(N-A)/2 at xf
  change ∀ i<d, g i=if i+1<d then 2^i*(2*A) else -((2*N+1)-(2*V-1))/2 at ug
  change ∀ i<c, g (d+i)=if i+1<c then 2^i*(2*V-1) else -((2*N+1)-(2*W-1-Z))/2 at vg
  change ∀ i<b, g (d+c+i)=if i+1<b then 2^i*(2*W-1-Z) else -((2*N+1)-(2*X-1-T-T*Z))/2 at wg
  change ∀ i<a, g (d+c+b+i)=if i+1<a then 2^i*(2*X-1-T-T*Z) else -((2*N+1)-A)/2 at xg
  have rel : D*A=N+V ∧ Z*V=N+W ∧ T*W=N+X ∧ R*X=N+A := by
    dsimp [A,V,W,X,N,C]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have grel : D*(2*A)=2*N+1+(2*V-1) ∧
      Z*(2*V-1)=2*N+1+(2*W-1-Z) ∧
      T*(2*W-1-Z)=2*N+1+(2*X-1-T-T*Z) ∧
      R*(2*X-1-T-T*Z)=2*N+1+A := by
    dsimp [A,V,W,X,N,C]; refine ⟨?_,?_,?_,?_⟩ <;> ring
  have nu := negative_step N A V ((2:ℤ)^(d-1)) (by rw [←hD]; exact rel.1)
  have nv := negative_step N V W ((2:ℤ)^(c-1)) (by rw [←hZ]; exact rel.2.1)
  have nw := negative_step N W X ((2:ℤ)^(b-1)) (by rw [←hT]; exact rel.2.2.1)
  have nx := negative_step N X A ((2:ℤ)^(a-1)) (by rw [←hR]; exact rel.2.2.2)
  have ngu := negative_step (2*N+1) (2*A) (2*V-1) ((2:ℤ)^(d-1))
    (by rw [←hD]; exact grel.1)
  have ngv := negative_step (2*N+1) (2*V-1) (2*W-1-Z) ((2:ℤ)^(c-1))
    (by rw [←hZ]; exact grel.2.1)
  have ngw := negative_step (2*N+1) (2*W-1-Z) (2*X-1-T-T*Z) ((2:ℤ)^(b-1))
    (by rw [←hT]; exact grel.2.2.1)
  have ngx := negative_step (2*N+1) (2*X-1-T-T*Z) A ((2:ℤ)^(a-1))
    (by rw [←hR]; exact grel.2.2.2)
  change (∀ i<d, 2*f i-g i=(if i+1<d then 0 else 1) ∧
      g i-f i=(if i+1<d then 2^i*A else -(2^(d-1)*R*T*Z)+2^(d-1)*C)) ∧
    (∀ i<c, 2*f (d+i)-g (d+i)=(if i+1<c then 2^i else 2^(c-1)+1) ∧
      g (d+i)-f (d+i)=(if i+1<c then 2^i*(2*(2^(d-1)*C))
        else -(2^(d-1)*R*T*Z)+2^(d-1)*(R+1)*Z)) ∧
    (∀ i<b, 2*f (d+c+i)-g (d+c+i)=
        (if i+1<b then 2^i*(Z+1) else 2^(b-1)*(Z+1)+1) ∧
      g (d+c+i)-f (d+c+i)=(if i+1<b then 2^i*(2*(2^(d-1)*(R+1)*Z))
        else -(2^(d-1)*R*T*Z)+2^(d-1)*T*Z)) ∧
    (∀ i<a, 2*f (d+c+b+i)-g (d+c+b+i)=
        (if i+1<a then 2^i*(T*Z+T+1) else 2^(a-1)*(T*Z+T+1)+1) ∧
      g (d+c+b+i)-f (d+c+b+i)=
        (if i+1<a then 2^i*(2*(2^(d-1)*T*Z)) else -(2^(d-1)*R*T*Z))) ∧
    g (d+c+b+a)=A
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro i hi
    rw [uf i hi,ug i hi]
    split_ifs with h
    · constructor <;> ring
    · rw [nu,ngu]
      constructor
      · ring
      · dsimp [V,A,C]; rw [hD]; ring
  · intro i hi
    rw [vf i hi,vg i hi]
    split_ifs with h
    · dsimp [V,C]; rw [hD]; constructor <;> ring
    · rw [nv,ngv]
      dsimp [W,V,C]; rw [hD,hZ]
      constructor <;> ring
  · intro i hi
    rw [wf i hi,wg i hi]
    split_ifs with h
    · dsimp [W]; rw [hD]; constructor <;> ring
    · rw [nw,ngw]
      dsimp [X,W]; rw [hD,hT]
      constructor <;> ring
  · intro i hi
    rw [xf i hi,xg i hi]
    split_ifs with h
    · dsimp [X]; rw [hD]; constructor <;> ring
    · rw [nx,ngx]
      dsimp [A,X,C]; rw [hD,hR]
      constructor <;> ring
  · convert fresh using 1 <;> dsimp [N,A,C,D,R,T,Z] <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
