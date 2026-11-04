/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakLowU/Selection
   generality: I
   mirror-B: none(waiver:consumed-low-u-support)
   mirror-E: none(waiver:physical-low-u-construction)
   anchors: []
   utility: none
   digest: Integer ceiling selection and all six strict physical windows. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Arithmetic

/-! Integer ceiling selection and all six strict physical windows. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
open private A B L K C SU SV SW window strict_polynomials strict_w_polynomials
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU.Arithmetic

private theorem strict_w_select (x y s z : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (hs : 2≤s) (hz : 8*s*y≤z)
    (hgap : y=2*x ∨ y=4*x ∨ 8*x≤y) :
    ∃ w : ℕ, 2*(w : ℤ)<y ∧
      A x y z+C y z ≤ K y s z-w*L x y s z ∧
      2*(K y s z-w*L x y s z)≤K y s z := by
  have polys := strict_polynomials x y s z hx hy hs hz
  have wp := strict_w_polynomials x y s z hx hs hz
  rcases hgap with h|h|h
  · exact ⟨1,by norm_num; omega,by simpa using (wp.1 h).1,by norm_num only [Nat.cast_one]; nlinarith [(wp.1 h).2]⟩
  · exact ⟨2,by norm_num; omega,by simpa using (wp.2.1 h).1,by norm_num only [Nat.cast_ofNat]; nlinarith [(wp.2.1 h).2]⟩
  · have hy0 : 0≤y := by omega
    have hs0 : 0≤s := by omega
    have hz0 : 0≤z := by nlinarith
    have hL : 0<L x y s z := by dsimp [L]; positivity
    have hK : 0≤K y s z := by dsimp [K]; positivity
    let q := K y s z/L x y s z
    have hq0 : 0≤q := Int.ediv_nonneg hK hL.le
    have hq4 : 4≤q := (Int.le_ediv_iff_mul_le hL).mpr (by nlinarith [wp.2.2 h])
    have hrem0 := Int.emod_nonneg (K y s z) (by omega : L x y s z≠0)
    have hrem1 := Int.emod_lt_of_pos (K y s z) hL
    have hdiv := Int.mul_ediv_add_emod (K y s z) (L x y s z)
    have hqeq : (q.toNat : ℤ)=q := Int.toNat_of_nonneg hq0
    refine ⟨q.toNat-1,?_,?_,?_⟩
    all_goals have hw : ((q.toNat-1 : ℕ) : ℤ)=q-1 := by omega
    all_goals rw [hw]
    · have hp := polys.2.2.2.2.2.2.2
      have hbound : 2*q≤y := by
        have hmul := mul_nonneg (show 0≤K y s z-q*L x y s z by dsimp [q]; nlinarith only [hrem0,hdiv]) (by norm_num : (0:ℤ)≤2)
        nlinarith only [hp,hmul,hL]
      omega
    · have hp := polys.2.2.2.2.2.2.1
      dsimp [q] at *
      nlinarith only [hrem0,hdiv,hp]
    · have hp := wp.2.2 h
      dsimp [q] at *
      nlinarith only [hrem1,hdiv,hp]

set_option maxHeartbeats 1600000 in
private theorem strict_select (x y s z : ℤ)
    (hx : 4≤x) (hy : 2*x≤y) (hs : 2≤s) (hz : 8*s*y≤z)
    (hgap : y=2*x ∨ y=4*x ∨ 8*x≤y) :
    ∃ u v w : ℕ, (u : ℤ)=s-1 ∧ 1≤v ∧ 2*(v : ℤ)<z ∧ 2*(w : ℤ)<y ∧
      window (L x y s z-v*B x y s) (L x y s z) ∧
      window (K y s z-w*L x y s z+u*A x y z-v*B x y s) (K y s z) ∧
      window ((u+1 : ℤ)*A x y z-v*B x y s) (A x y z) ∧
      window (SV x y s z-v*SU x y s) (SV x y s z) ∧
      window (SW y s z-w*SV x y s z+(2*u+1 : ℤ)*A x y z-v*SU x y s) (SW y s z) ∧
      window ((2*u+2 : ℤ)*A x y z-v*SU x y s) (A x y z) := by
  obtain ⟨w,hw,hR,hRupper⟩ := strict_w_select x y s z hx hy hs hz hgap
  obtain ⟨hA3,hSU16,hP,hLupper,hstock,hAC,hLC,hKL⟩ := strict_polynomials x y s z hx hy hs hz
  have hy0 : 0≤y := by omega
  have hs0 : 0≤s := by omega
  have hz0 : 0≤z := by nlinarith
  have hA : 0<A x y z := by dsimp [A]; positivity
  have hC : 0≤C y z := by dsimp [C]; positivity
  have hSU : 0<SU x y s := by omega
  let V := ((4*s-1)*A x y z+2*SU x y s)/(2*SU x y s)
  have rem0 := Int.emod_nonneg ((4*s-1)*A x y z+2*SU x y s)
    (by omega : 2*SU x y s≠0)
  have rem1 := Int.emod_lt_of_pos ((4*s-1)*A x y z+2*SU x y s)
    (by omega : 0<2*SU x y s)
  have div := Int.mul_ediv_add_emod ((4*s-1)*A x y z+2*SU x y s) (2*SU x y s)
  have ceil : (4*s-1)*A x y z+1≤2*V*SU x y s ∧
      2*V*SU x y s≤(4*s-1)*A x y z+2*SU x y s := by
    dsimp [V]; constructor <;> nlinarith only [rem0,rem1,div]
  have vpos : 1≤V := by
    apply (Int.le_ediv_iff_mul_le (show 0<2*SU x y s by omega)).mpr
    have hmul : 0≤(4*s-1)*A x y z := mul_nonneg (by omega) hA.le
    nlinarith only [hmul]
  let E := 2*s*A x y z-V*SU x y s
  have Ebounds : A x y z-2*SU x y s≤2*E ∧ 2*E≤A x y z-1 := by
    dsimp [E]; constructor <;> nlinarith only [ceil.1,ceil.2]
  have E6 : A x y z≤6*E := by omega
  have EV : V≤E := by
    have hV : 0≤V := by omega
    have p := mul_nonneg hV (show 0≤SU x y s-16*s by omega)
    have q : 0≤s*(A x y z-8*V) := by
      dsimp [E] at *
      nlinarith only [p,E6,hA]
    have : 8*V≤A x y z := by nlinarith only [q,hs]
    omega
  have vstock : 2*V<z := by
    have hl : V*SU x y s≤2*s*A x y z := by dsimp [E] at *; omega
    have hh : (2*V-z)*SU x y s<0 := by nlinarith only [hl,hstock]
    nlinarith only [hh,hSU]
  have castV : (V.toNat : ℤ)=V := Int.toNat_of_nonneg (by omega)
  have castU : ((s-1).toNat : ℤ)=s-1 := Int.toNat_of_nonneg (by omega)
  refine ⟨(s-1).toNat,V.toNat,w,castU,?_,?_,hw,?_,?_,?_,?_,?_,?_⟩
  · omega
  · simpa only [castV] using vstock
  all_goals simp only [window,Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_ofNat,castV,castU]
  all_goals have Ee : E=2*s*A x y z-V*SU x y s := rfl
  all_goals have SUe : SU x y s=2*B x y s-1 := rfl
  all_goals have SVe : SV x y s z=2*L x y s z-1-z := rfl
  all_goals have SWe : SW y s z=2*K y s z-C y z := rfl
  all_goals have Ce : C y z=1+y+y*z := rfl
  all_goals have hw0 : (0 : ℤ)≤w := by positivity
  all_goals have wpos := mul_nonneg hw0 (show 0≤1+z by omega)
  all_goals have wcap := mul_nonneg (show 0≤y-2*(w : ℤ) by omega) (show 0≤1+z by omega)
  all_goals dsimp [SU,SV,SW,C] at *
  all_goals constructor
  all_goals nlinarith only [Ebounds.1,Ebounds.2,E6,EV,Ee,SUe,SVe,SWe,Ce,
    hP,hLupper,hR,hRupper,hA,hC,hAC,vpos,hw,wpos,wcap]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakLowU
