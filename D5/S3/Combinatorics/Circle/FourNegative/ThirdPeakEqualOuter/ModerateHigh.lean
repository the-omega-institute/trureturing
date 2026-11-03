import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModeratePhysical

/-! UNELABORATED. The high-V quotient is decoded at physical offset a+(c-a).
Its selected mask is contained in the complete high stock, with an XOR complement. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
open private A B L K SU SV SW Window pow_lower pow_split
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Arithmetic
open private F G nextF nextG positive_rows native_rows Joint
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.Source
open private FirstTwoWindows moderate_W moderate_high_selector
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModerateArithmetic
open private moderate_realize moderateHighBanks moderate_high_inventory
  moderate_high_positive moderate_high_masses
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter.ModeratePhysical
open private full terminals v_stock_masks
  from D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPaidV.Banks
open private chainLength oldValue newValue
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private theorem moderate_parameters (a b c : ℕ) (hb : 2 ≤ b) (hba : b < a)
    (hac : a < c) (hmod : c ≤ a+b-2) :
    (8:ℤ) ≤ 2^b ∧ (2:ℤ)*2^b ≤ 2^a ∧ (2:ℤ) ≤ 2^(c-a) ∧
    4*(2:ℤ)^(c-a) ≤ 2^b ∧
    ((2:ℤ)^(c-a)=2 ∨ 4 ≤ (2:ℤ)^(c-a)) ∧
    (2:ℤ)^c=2^(c-a)*2^a := by
  have hy : (8:ℤ) ≤ 2^b := by simpa using pow_lower b 3 (by omega)
  have hx := pow_lower (a-b) 1 (by omega)
  have hxb : (2:ℤ)*2^b ≤ 2^a := by
    rw [pow_split a b (by omega)]
    have hp : 0 ≤ (2:ℤ)^b := by positivity
    nlinarith only [mul_nonneg (show 0 ≤ (2:ℤ)^(a-b)-2 by simpa using sub_nonneg.mpr hx) hp]
  have hm : (2:ℤ) ≤ 2^(c-a) := by simpa using pow_lower (c-a) 1 (by omega)
  have hmy : 4*(2:ℤ)^(c-a) ≤ 2^b := by
    calc
      4*(2:ℤ)^(c-a)=(2:ℤ)^(c-a+2) := by rw [pow_add]; norm_num; ring
      _ ≤ 2^b := pow_lower b (c-a+2) (by omega)
  have hmcase : (2:ℤ)^(c-a)=2 ∨ 4 ≤ (2:ℤ)^(c-a) := by
    by_cases h : c=a+1
    · left; rw [show c-a=1 by omega]; norm_num
    · right; simpa using pow_lower (c-a) 2 (by omega)
  exact ⟨hy,hxb,hm,hmy,hmcase,pow_split c a (by omega)⟩

set_option maxHeartbeats 1800000 in
private theorem moderate_high_joint (a b c : ℕ) (hb : 2 ≤ b) (hba : b+2 ≤ a)
    (hac : a < c) (hmod : c ≤ a+b-2) : Joint a b c := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let z : ℤ := 2^c
  let m : ℤ := 2^(c-a)
  obtain ⟨hy,hx2,hm,hmy,hmcase,hz⟩ := moderate_parameters a b c hb (by omega) hac hmod
  change z=m*x at hz
  have hx4 : 4*y ≤ x := by
    have hp := pow_lower (a-b) 2 (by omega)
    change 4 ≤ (2:ℤ)^(a-b) at hp
    change 4*(2:ℤ)^b ≤ (2:ℤ)^a
    rw [pow_split a b (by omega)]
    nlinarith [mul_nonneg (show 0 ≤ (2:ℤ)^(a-b)-4 by omega) (show 0 ≤ (2:ℤ)^b by positivity)]
  obtain ⟨h,hh,hhcap,hw⟩ := moderate_high_selector x y m hy hx4 hm hmy
  let hn := h.toNat
  have eh : (hn:ℤ)=h := Int.toNat_of_nonneg hh
  have hcap : hn < 2^(a-1) := by
    have hp : x=2*(2:ℤ)^(a-1) := by
      dsimp [x]; conv_lhs => rw [show a=(a-1)+1 by omega,pow_succ]; ring
    have : (hn:ℤ) < (2:ℤ)^(a-1) := by rw [eh]; omega
    exact_mod_cast this
  let early := decide (m=2)
  let P := moderateHighBanks a b c hn
  let C := fun j : Fin 4 => (full a b c a j : ℤ)
  let E := m*B x y-A x y z
  let Ep := 2*E-m
  let R := L x z-A x y z-h*m*B x y
  let Rp := 2*R-z-1+m*h
  have wfirst : FirstTwoWindows x y z E Ep R Rp := by
    simpa only [E,Ep,R,Rp,hz] using hw
  obtain ⟨wW,wWn⟩ := moderate_W x y m hy hx2 hmcase
  have wW' : Window (K x y z-A x y z) (K x y z) := by simpa only [hz] using wW
  have wWn' : Window (SW x y z-2*A x y z+(if early then A x y z else 0)) (SW x y z) := by
    simpa [early,hz] using wWn
  have hmasses (f : ℕ → ℤ) (H : Fin 4 → ℤ)
      (hf : ∀ j : Fin 4, ∀ e < chainLength a b c a j-1,
        f ((![0,a,a+c,a+c+b] : Fin 4 → ℕ) j+e)=2^e*H j) :=
    moderate_high_masses a b c hn (by omega) (by omega) hcap f H hf
  have mo := hmasses (oldValue a b c a) (F x y z) (positive_rows a b c (by omega) hb (by omega)).1
  have mn := hmasses (newValue a b c a) (G x y z) (positive_rows a b c (by omega) hb (by omega)).2
  rw [eh] at mo mn
  have nu := native_rows a b c (by omega) hb (by omega) 0
  have nv := native_rows a b c (by omega) hb (by omega) 1
  have nw := native_rows a b c (by omega) hb (by omega) 2
  dsimp only [F,G,nextF,nextG,terminals] at nu nv nw
  have hC : C 1=(m-1)+m*C 0 := by
    have ht := v_stock_masks c a (by omega) (by omega)
    have hh' := congrArg (fun t : ℕ => (t:ℤ)) ht
    simpa only [C,full,chainLength,Nat.cast_add,Nat.cast_mul,
      Nat.cast_sub (show 1 ≤ 2^(c-1) by have := Nat.two_pow_pos (c-1); omega),
      Nat.cast_sub (show 1 ≤ 2^(c-a) by have := Nat.two_pow_pos (c-a); omega),
      Nat.cast_sub (show 1 ≤ 2^(a-1) by have := Nat.two_pow_pos (a-1); omega),
      Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hh'
  change ((P 0).map (oldValue a b c a)).sum=C 0*A x y z+(m-1)*B x y ∧
    ((P 1).map (oldValue a b c a)).sum=m*(C 0-h)*B x y ∧
    ((P 2).map (oldValue a b c a)).sum=C 2*L x z+m*h*B x y ∧
    ((P 3).map (oldValue a b c a)).sum=C 3*K x y z at mo
  change ((P 0).map (newValue a b c a)).sum=C 0*(2*A x y z)+(m-1)*SU x y ∧
    ((P 1).map (newValue a b c a)).sum=m*(C 0-h)*SU x y ∧
    ((P 2).map (newValue a b c a)).sum=C 2*SV x z+m*h*SU x y ∧
    ((P 3).map (newValue a b c a)).sum=C 3*SW x y z at mn
  apply moderate_realize a b c (by omega) hb (by omega) P early E Ep R Rp
    (moderate_high_inventory a b c hn (by omega) hb (by omega))
    (moderate_high_positive a b c hn (by omega) hb (by omega))
  · dsimp [E]; nlinarith only [mo.1,nu.1]
  · dsimp [Ep,E,SU] at *; nlinarith only [mn.1,nu.2.1]
  · dsimp [E,R]
    have hcB := congrArg (fun t : ℤ => t*B x y) hC
    nlinarith only [mo.2.1,nu.1,nv.1,hcB]
  · dsimp [Ep,E,Rp,R,SU,SV] at *
    have hcU := congrArg (fun t : ℤ => t*SU x y) hC
    dsimp [SU] at hcU
    nlinarith only [mn.2.1,nu.2.1,nv.2.1,hcU,hz]
  · dsimp [R]; nlinarith only [mo.2.2.1,nw.1]
  · dsimp [Rp,R,SU,SV,SW] at *; nlinarith only [mn.2.2.1,nw.2.1,hz]
  · exact wfirst
  · exact wW'
  · exact wWn'

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualOuter
