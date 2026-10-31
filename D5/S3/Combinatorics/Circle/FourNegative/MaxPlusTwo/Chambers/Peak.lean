/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Peak
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/Peak
   mirror-E: none(waiver:consumed-chamber-arithmetic)
   anchors: [mathlib/module/Mathlib.Data.Int.DivMod]
   utility: none
   digest: Adjacent dyadic peak chamber with an advanced physical V mask. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
import Mathlib.Tactic.Ring

/-! Advancing V creates the exact grid step Delta=8A-2e1. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private ceilpos ceilpos_bounds
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

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
