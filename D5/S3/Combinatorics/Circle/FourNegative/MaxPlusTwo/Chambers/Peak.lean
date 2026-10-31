/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Peak
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Peak
   mirror-E: none(waiver:consumed-chamber-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Adjacent dyadic peak chamber with an advanced physical V mask. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
import Mathlib.Tactic.Ring
import Batteries.Tactic.OpenPrivate

/-! Advancing V creates the exact grid step Delta=8A-2e1. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private ceilpos ceilpos_bounds mass_margin
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic

private theorem peak_advance_polynomials (R P : ℤ) (hR : 4≤R) (hP : 2≤P) :
    let Z:=2*P
    let C:=2*R*Z+R+1
    let A:=2*R*Z^2+C
    let e:=4*Z*C
    let delta:=8*A-2*e
    0<delta ∧ 0<e-3*A ∧ delta<e-A ∧
      e-3*A≤delta*(P-1) := by
  dsimp only
  have hr : 0≤R-4 := by omega
  have hp : 0≤P-2 := by omega
  generalize hr0 : R-4=r at hr
  generalize hp0 : P-2=p at hp
  have heR : R=r+4 := by omega
  have heP : P=p+2 := by omega
  rw [heR,heP]
  constructor
  · ring_nf; positivity
  constructor
  · ring_nf; positivity
  constructor
  · apply sub_pos.mp
    ring_nf; positivity
  · apply sub_nonneg.mp
    ring_nf; positivity

/-- Exact reserve and physical capacity for T=2Z, including the double ratio boundary. -/
private theorem peak_advance_bounds (R P : ℤ) (hR : 4≤R) (hP : 2≤P) :
    let Z:=2*P
    let C:=2*R*Z+R+1
    let A:=2*R*Z^2+C
    let e:=4*Z*C
    let delta:=8*A-2*e
    let n:=ceilpos (e-3*A) delta
    1≤n ∧ (n:ℤ)≤P-1 ∧
      e≤A*(8*n+3)-2*e*n ∧ A*(8*n+3)-2*e*n≤2*e-A ∧
      (8*n+3:ℤ)≤4*Z-5 := by
  dsimp only
  let Z:=2*P
  let C:=2*R*Z+R+1
  let A:=2*R*Z^2+C
  let e:=4*Z*C
  let delta:=8*A-2*e
  let n:=ceilpos (e-3*A) delta
  have hp := peak_advance_polynomials R P hR hP
  change 0<delta ∧ 0<e-3*A ∧ delta<e-A ∧ e-3*A≤delta*(P-1) at hp
  have hn := ceilpos_bounds (e-3*A) delta hp.1
  change e-3*A≤delta*(n:ℤ) ∧ (0<n → delta*((n:ℤ)-1)<e-3*A) at hn
  have hnpos : 0<n := by
    by_contra h
    have hz : n=0 := by omega
    rw [hz] at hn; norm_num at hn; omega
  have hcap : (n:ℤ)≤P-1 := by
    by_contra h
    have hstep : P-1≤(n:ℤ)-1 := by omega
    have hm:=mul_le_mul_of_nonneg_left hstep hp.1.le
    nlinarith [hn.2 hnpos]
  change 1≤n ∧ (n:ℤ)≤P-1 ∧
    e≤A*(8*n+3)-2*e*n ∧ A*(8*n+3)-2*e*n≤2*e-A ∧
    (8*n+3:ℤ)≤4*Z-5
  have hid : A*(8*n+3)-2*e*n=3*A+delta*n := by dsimp [delta]; ring
  rw [hid]
  refine ⟨by omega,hcap,by nlinarith [hn.1],?_,?_⟩
  · nlinarith [hn.2 hnpos,hp.2.2.1]
  · dsimp [Z]; omega


/-- The middle peak seam chooses the literal low mask two or three. -/
private theorem peak_middle_bounds (R T Z : ℤ) (hR : 4≤R) (hT : 4≤T) (hZ : 4≤Z) :
    let C:=R*T+R+1
    let A:=R*T*Z+C
    let e:=2*T*(R+1)*Z
    (Z≤R → e≤2*A ∧ 2*A≤2*e-A) ∧
      (2*R≤Z → e≤3*A ∧ 3*A≤2*e-A) := by
  have hm := mass_margin R T Z hR hT hZ
  have hT0 : 0≤T := by omega
  have hZ0 : 0≤Z := by omega
  dsimp only
  constructor
  · intro hZR
    have h := mul_nonneg hT0 (show 0≤R-Z by omega)
    constructor <;> nlinarith [mul_nonneg hT0 hZ0]
  · intro hRZ
    constructor
    · have h := mul_nonneg (mul_nonneg hT0 hZ0) (show 0≤R-2 by omega)
      nlinarith
    · have h := mul_nonneg hT0 (show 0≤Z-2*R by omega)
      have h' := mul_nonneg (show 0≤T-4 by omega) (show 0≤R by omega)
      nlinarith

/-- A high disjoint U bit and either low mask fit the first peak reserve interval. -/
private theorem peak_direct_reserve (m C e H s : ℤ)
    (hC : 0≤C) (hm : 3*C<m) (hH : 8≤H) (hs : 2≤s ∧ s≤3)
    (he0 : H*m≤e) (he1 : e≤H*(m+C)) :
    e≤(m+C)*(H+s) ∧ (m+C)*(H+s)≤2*e-(m+C) := by
  have hA : 0≤m+C := by omega
  have hpos := mul_nonneg hA (show 0≤s by omega)
  have hgrid := mul_nonneg (show 0≤H-8 by omega) (show 0≤m-C by omega)
  have hlow := mul_nonneg hA (show 0≤3-s by omega)
  constructor <;> nlinarith


/-- The complete direct peak first seam and its physical U capacity. -/
private theorem peak_direct_bounds (R T Z H s : ℤ)
    (hR : 4≤R) (hT : 4≤T) (hZ : 4≤Z) (hH : 8≤H)
    (hs : 2≤s ∧ s≤3) (hratio : Z*H=2*T) :
    let C:=R*T+R+1
    let A:=R*T*Z+C
    let e:=2*T*C
    e≤A*(H+s) ∧ A*(H+s)≤2*e-A ∧ H+s<2*T := by
  let C:=R*T+R+1
  let m:=R*T*Z
  let e:=2*T*C
  have hm := mass_margin R T Z hR hT hZ
  have hC : 0≤C := by
    dsimp [C]
    nlinarith [mul_nonneg (show 0≤R by omega) (show 0≤T by omega)]
  have hCZ : Z*(R+1)≤C := by
    have hT4Z : 4*Z≤T := by
      have h := mul_nonneg (show 0≤Z by omega) (show 0≤H-8 by omega)
      nlinarith only [h,hratio]
    have h := mul_nonneg (show 0≤R by omega) (show 0≤T-4*Z by omega)
    have h' := mul_nonneg (show 0≤R-1 by omega) (show 0≤Z by omega)
    dsimp [C]
    nlinarith only [h,h',hR,hZ]
  have hbase : H*m=2*T*(R*T) := by
    calc
      H*m=(Z*H)*(R*T) := by dsimp [m]; ring
      _=2*T*(R*T) := by rw [hratio]
  have he0 : H*m≤e := by
    have h := mul_nonneg (show 0≤2*T by omega) (show 0≤R+1 by omega)
    dsimp [e,C]
    nlinarith only [hbase,h]
  have he1 : e≤H*(m+C) := by
    have h := mul_le_mul_of_nonneg_left hCZ (show 0≤H by omega)
    have heq : H*(Z*(R+1))=2*T*(R+1) := by
      calc
        H*(Z*(R+1))=(Z*H)*(R+1) := by ring
        _=2*T*(R+1) := by rw [hratio]
    rw [heq] at h
    dsimp [e,C] at *
    nlinarith only [hbase,h]
  have hb := peak_direct_reserve m C e H s hC hm hH hs he0 he1
  change e≤(m+C)*(H+s) ∧ (m+C)*(H+s)≤2*e-(m+C) ∧ H+s<2*T
  refine ⟨hb.1,hb.2,?_⟩
  have h := mul_nonneg (show 0≤Z-4 by omega) (show 0≤H by omega)
  nlinarith only [h,hratio,hH,hs.2]

/-- At T=2R the third block releases all U bits and reserves the lowest W bit. -/
private theorem peak_double_end (R Z : ℤ) (hR : 4≤R) (hZ : 4≤Z) :
    let C:=2*R^2+R+1
    let A:=2*R^2*Z+C
    let e2:=4*R*(R+1)*Z
    let e3:=8*R^2*Z
    e3≤2*e2 ∧ 2*e2≤2*e3-A := by
  dsimp only
  have hr : 0≤R-4 := by omega
  have hz : 0≤Z-4 := by omega
  generalize hr0 : R-4=r at hr
  generalize hz0 : Z-4=z at hz
  have heR : R=r+4 := by omega
  have heZ : Z=z+4 := by omega
  rw [heR,heZ]
  constructor <;> apply sub_nonneg.mp <;> ring_nf <;> positivity

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
