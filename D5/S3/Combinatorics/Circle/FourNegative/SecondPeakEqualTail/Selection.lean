/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Selection
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: All six unbounded selector branches with every original paired terminal window. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SelectorMasks
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.LargeWindows
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.MiddleWindows
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SmallLessWindows
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SmallGeWindows
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SpecialWindows

/-! The branches are exhaustive in exponent space; no bounded gap search is used. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open private MaskBounds large_masks middle_masks small_less_masks small_ge_masks
  special_high_masks special_point_masks from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SelectorMasks
open private scaledGates A B L K SU SV SW from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Algebra
open private large_windows from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.LargeWindows
open private middle_windows from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.MiddleWindows
open private small_l_less_windows from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SmallLessWindows
open private small_l_ge_windows from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SmallGeWindows
open private special_high_windows from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.SpecialWindows

private def selectorGates (a r t alpha m0 v j0 : ℕ) (early : Bool) : Fin 12 → ℤ :=
  scaledGates ((2:ℤ)^a) ((2:ℤ)^r) ((2:ℤ)^t)
    alpha (4*(m0:ℤ)) (4*(v:ℤ)) (4*(j0:ℤ)) (if early then 1 else 0)

private theorem pow_split (r l : ℕ) :
    (2:ℤ)^(r+l+2)=4*2^r*2^l := by
  rw [pow_add,pow_add]
  norm_num
  ring

set_option maxHeartbeats 1500000 in
private theorem selector_exists (a r t : ℕ) (ha : 2≤a) (hr : 1≤r) :
    ∃ alpha m0 v j0 : ℕ, ∃ early : Bool,
      MaskBounds a (a+r) alpha m0 v j0 ∧
      ∀ i : Fin 12, 0≤selectorGates a r t alpha m0 v j0 early i := by
  have hs : (1:ℤ)≤2^t := one_le_pow₀ (by norm_num)
  have hp : (2:ℤ)≤2^r := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hr
    norm_num at h ⊢
    exact h
  have hx : (4:ℤ)≤2^a := by
    have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) ha
    norm_num at h ⊢
    exact h
  have quarter : 4*(2:ℤ)^(a-2)=2^a := by
    rw [show a=(a-2)+2 by omega,pow_add]
    norm_num
    ring
  have half : 2*(2:ℤ)^(a-1)=2^a := by
    calc
      2*(2:ℤ)^(a-1)=(2:ℤ)^((a-1)+1) := by rw [pow_succ]; ring
      _=(2:ℤ)^a := by congr 1; omega
  by_cases hlarge : a≤r
  · refine ⟨0,2^r-1,2^(a-2),2^(a-1),false,large_masks a r ha hlarge,?_⟩
    have hpx := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) hlarge
    intro i
    dsimp [selectorGates]
    simp only [Nat.cast_zero,Nat.cast_sub (Nat.one_le_two_pow : 1≤(2:ℕ)^r),
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
    have hm4 : (4:ℤ) * (2^r-1) = 4*(2:ℤ)^r-4 := by ring
    have hv4 : (4:ℤ) * (2:ℤ)^(a-2) = (2:ℤ)^a := by
      nlinarith only [quarter]
    have hj4 : (4:ℤ) * (2:ℤ)^(a-1) = 2*(2:ℤ)^a := by
      nlinarith only [half]
    rw [hm4,hv4,hj4]
    exact large_windows ((2:ℤ)^a) ((2:ℤ)^r) ((2:ℤ)^t) hx hpx hs i
  by_cases hmiddle : r=a-1
  · subst r
    by_cases ha2 : a=2
    · subst a
      by_cases ht : t=0
      · subst t
        refine ⟨1,6,2,4,true,special_point_masks,?_⟩
        intro i
        fin_cases i <;> norm_num [selectorGates,scaledGates,A,B,L,K,SU,SV,SW]
      · refine ⟨0,2,1,2,true,special_high_masks,?_⟩
        have hs2 : (2:ℤ)≤2^t := by
          have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 1≤t by omega)
          norm_num at h ⊢
          exact h
        intro i
        simpa [selectorGates,scaledGates,A,B,L,K,SU,SV,SW] using
          special_high_windows ((2:ℤ)^t) hs2 i
    · have ha3 : 3≤a := by omega
      refine ⟨0,2^a-2,2^(a-2)+1,2^(a-1)+2,true,middle_masks a ha3,?_⟩
      have hp4 : (4:ℤ)≤2^(a-1) := by
        have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show 2≤a-1 by omega)
        norm_num at h ⊢
        exact h
      intro i
      dsimp [selectorGates]
      simp only [Nat.cast_zero,Nat.cast_sub (show 2≤(2:ℕ)^a by
        have h := Nat.pow_le_pow_right (by decide : 0<2) (show 1≤a by omega)
        norm_num at h ⊢; exact h),
        Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
      have hxeq : (2:ℤ)^a = 2*(2:ℤ)^(a-1) := half.symm
      have hmeq : (4:ℤ)*((2:ℤ)^a-2) = 8*(2:ℤ)^(a-1)-8 := by
        nlinarith only [half]
      have hveq : (4:ℤ)*((2:ℤ)^(a-2)+1) = 2*(2:ℤ)^(a-1)+4 := by
        nlinarith only [quarter,half]
      have hjeq : (4:ℤ)*((2:ℤ)^(a-1)+2) = 4*(2:ℤ)^(a-1)+8 := by ring
      rw [hmeq,hveq,hjeq,hxeq]
      exact middle_windows ((2:ℤ)^(a-1)) ((2:ℤ)^t) hp4 hs i
  have har : r+2≤a := by omega
  obtain ⟨l,hal⟩ := Nat.exists_eq_add_of_le har
  have ae : a=r+l+2 := by omega
  subst a
  have he : (1:ℤ)≤2^l := one_le_pow₀ (by norm_num)
  have xeq := pow_split r l
  have jexp : r+l+2-1=r+l+1 := by omega
  have jrel : 4*((2:ℤ)^(r+l+1)+2^(l+1))=
      2*(2:ℤ)^(r+l+2)+8*2^l := by
    rw [pow_succ,pow_succ,pow_split]
    ring
  by_cases hl : l<r
  · refine ⟨2^l,2*2^r*(2^l+1)-2,2^l*(2^r+1),
      2^(r+l+1)+2^(l+1),true,by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using small_less_masks r l hr hl,?_⟩
    have hpe : 2*(2:ℤ)^l≤2^r := by
      have h := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show l+1≤r by omega)
      rw [pow_succ] at h
      nlinarith
    have hm : 2≤2*(2:ℕ)^r*(2^l+1) := by
      have h1 := Nat.two_pow_pos r
      have h2 := Nat.two_pow_pos l
      nlinarith
    intro i
    dsimp [selectorGates]
    simp only [Nat.cast_sub hm,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_ofNat,Nat.cast_one]
    rw [show r+2+l=r+l+2 by omega,xeq,jrel]
    have hm4 : (4:ℤ)*(2*(2:ℤ)^r*((2:ℤ)^l+1)-2) =
        8*(2:ℤ)^r*((2:ℤ)^l+1)-8 := by ring
    have hv4 : (4:ℤ)*((2:ℤ)^l*((2:ℤ)^r+1)) =
        4*(2:ℤ)^r*(2:ℤ)^l+4*(2:ℤ)^l := by ring
    have hj4 : 2*(2:ℤ)^(r+l+2)+8*(2:ℤ)^l =
        8*(2:ℤ)^r*(2:ℤ)^l+8*(2:ℤ)^l := by
      rw [xeq]
      ring
    rw [hm4,hv4,hj4]
    exact small_l_less_windows ((2:ℤ)^l) ((2:ℤ)^r) ((2:ℤ)^t) he hpe hs i
  · have hrl : r≤l := by omega
    refine ⟨2^l+2^(l-r),2*2^r*(2^l+2^(l-r)+1)-2,2^l*(2^r+1),
      2^(r+l+1)+2^(l+1),true,by simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using small_ge_masks r l hr hrl,?_⟩
    have hh : (1:ℤ)≤2^(l-r) := one_le_pow₀ (by norm_num)
    have erel : (2:ℤ)^l=2^r*2^(l-r) := by
      rw [←pow_add]
      congr 1
      omega
    have hm : 2≤2*(2:ℕ)^r*(2^l+2^(l-r)+1) := by
      have h1 := Nat.two_pow_pos r
      have h2 := Nat.two_pow_pos l
      nlinarith
    intro i
    dsimp [selectorGates]
    simp only [Nat.cast_sub hm,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,
      Nat.cast_ofNat,Nat.cast_one]
    rw [show r+2+l=r+l+2 by omega,xeq,jrel,erel]
    have hxarg : 4*(2:ℤ)^r*((2:ℤ)^r*(2:ℤ)^(l-r)) =
        4*((2:ℤ)^r)^2*(2:ℤ)^(l-r) := by ring
    have hm4 : (4:ℤ)*(2*(2:ℤ)^r*((2:ℤ)^r*(2:ℤ)^(l-r)+
        (2:ℤ)^(l-r)+1)-2) =
        8*(2:ℤ)^r*((2:ℤ)^r*(2:ℤ)^(l-r)+(2:ℤ)^(l-r)+1)-8 := by ring
    have hv4 : (4:ℤ)*((2:ℤ)^r*(2:ℤ)^(l-r)*((2:ℤ)^r+1)) =
        4*((2:ℤ)^r)^2*(2:ℤ)^(l-r)+4*(2:ℤ)^r*(2:ℤ)^(l-r) := by ring
    have hpowl := xeq
    rw [erel] at hpowl
    have hj4 : 2*(2:ℤ)^(r+l+2)+8*((2:ℤ)^r*(2:ℤ)^(l-r)) =
        8*((2:ℤ)^r)^2*(2:ℤ)^(l-r)+8*(2:ℤ)^r*(2:ℤ)^(l-r) := by
      rw [hpowl]
      ring
    rw [hxarg,hm4,hv4,hj4]
    exact small_l_ge_windows ((2:ℤ)^r) ((2:ℤ)^(l-r)) ((2:ℤ)^t) hp hh hs i

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
