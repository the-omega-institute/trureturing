/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AscendingActual
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/AscendingActual
   mirror-E: none(waiver:internal-source-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual ascending physical inventory and Strong through low-bit reserve release. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AscendingMasks

/-! The rounded arithmetic is applied to the exact constructor and physical labels. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ old charge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private masked_inventory from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private actual_masked_strong
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
open private ceilpos from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Arithmetic
open private ascending_v_masks ascending_w_masks
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.AscendingMasks

set_option maxHeartbeats 1200000 in
private theorem ascending_actual (a b c : ℕ) (ha : 2≤a)
    (hab : a≤b) (hbc : b≤c) (hac : a<c) :
    (baseWord a b c).Perm (List.range (a+b+c+(c+2))) ∧
      Strong (old a b c (c+2)) (charge a b c (c+2))
        (2^(c+2-1)*2^a*2^b*2^c) 0 (seedZ a b c) (baseWord a b c) := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let A:=seedZ a b c
  let e1:=2*(Z:ℤ)*((R:ℤ)*T+R+1)
  let e2:=2*((R:ℤ)+1)*(Z:ℤ)^2
  let e3:=2*(T:ℤ)*(Z:ℤ)^2
  let v:=ceilpos (e2-3*A) (2*e1)
  let S:=3*A+2*e1*v
  let wl:=if 4*R≤T then (ceilpos (e3-S) (2*e2),0)
    else if T=2*R then
      if e3≤S then (0,0) else (1,ceilpos (S+2*e2-2*e3+A) A)
    else (0,ceilpos (S-2*e3+A) A)
  have hv:=ascending_v_masks a b c ha hab hbc hac
  change v<2^(c-1) ∧ 2*A<e1 ∧ e1≤3*A ∧ 3*A≤2*e1-A ∧ 2*A<e3 ∧
    e2≤S ∧ S≤2*e2-A ∧ S<e2+2*e1 at hv
  have hw:=ascending_w_masks a b c ha hab hbc hac
  change wl.1<2^(b-1) ∧ wl.2≤3 ∧
    e3≤S+2*e2*wl.1-A*wl.2 ∧ S+2*e2*wl.1-A*wl.2≤2*e3-A at hw
  have hx : (3 ^^^ wl.2)≤3 ∧ ((3 ^^^ wl.2:ℕ):ℤ)=3-(wl.2:ℤ) := by
    have he : wl.2=0 ∨ wl.2=1 ∨ wl.2=2 ∨ wl.2=3 := by omega
    rcases he with he|he|he|he <;> rw [he] <;> norm_num
  have hcap : 3<2^(c+1) := by
    have hh : 4≤(2:ℕ)^(c+1):=Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤c+1 by omega)
    omega
  have hbits : ∀ e, (3 ^^^ wl.2:ℕ).testBit e=true → (3:ℕ).testBit e=true := by
    intro e he
    have hlen : (3 ^^^ wl.2:ℕ)<2^2 := by omega
    have he2 : e<2 := by
      by_contra hh
      have hz:=Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlen (Nat.pow_le_pow_right Nat.zero_lt_two (show 2≤e by omega)))
      simp [hz] at he
    change (2^2-1:ℕ).testBit e=true
    simp only [Nat.testBit_two_pow_sub_one,decide_eq_true_eq]
    exact he2
  have hd : max (max a b) c+2=c+2 := by rw [max_eq_right hab,max_eq_right hbc]
  have hmono : min a c≤b ∧ b≤max a c := by rw [min_eq_left hac.le,max_eq_right hac.le]; exact ⟨hab,hbc⟩
  have hnot : ¬(c≤b ∧ b≤a) := by omega
  have hneq : ¬((2:ℕ)^a=2^b ∧ (2:ℕ)^b=2^c) := by
    intro he
    have hpow : (2:ℕ)^a<2^c:=Nat.pow_lt_pow_right (show 1<(2:ℕ) by decide) hac
    omega
  have hD : (2:ℤ)^(c+2)=4*(Z:ℤ) := by dsimp [Z]; push_cast; rw [pow_add]; norm_num; ring
  have hseed : (R:ℤ)*T*Z+(R:ℤ)*T+R+1=A := by dsimp [A,seedZ,R,T,Z]; push_cast; ring
  have hword : baseWord a b c=chamberMaskedWord a b c (c+2) 3 3 (3 ^^^ wl.2) 0 v v wl.1 := by
    dsimp only [baseWord,baseBlocks]
    rw [if_pos hmono]
    simp only [monotoneBlocks,if_neg hnot,if_neg hneq,hd]
    rw [hD,hseed]
    have he1 : 4*(Z:ℤ)*((R:ℤ)*T+R+1)/2=e1 := by
      have he : 4*(Z:ℤ)*((R:ℤ)*T+R+1)=2*e1 := by dsimp [e1]; ring
      rw [he]; omega
    have he2 : 4*(Z:ℤ)*((R:ℤ)+1)*Z/2=e2 := by
      have he : 4*(Z:ℤ)*((R:ℤ)+1)*Z=2*e2 := by dsimp [e2]; ring
      rw [he]; omega
    have he3 : 4*(Z:ℤ)*(T:ℤ)*Z/2=e3 := by
      have he : 4*(Z:ℤ)*(T:ℤ)*Z=2*e3 := by dsimp [e3]; ring
      rw [he]; omega
    rw [he1,he2,he3]
    rfl
  rw [hword]
  constructor
  · apply masked_inventory a b c (c+2) 3 3 (3 ^^^ wl.2) 0 v v wl.1
      (by omega) (by omega) (by omega) (by omega)
    · intro e _ he; exact he
    · intro e _ he; exact hbits e he
    · intro e he _; simp [Nat.testBit_two_pow_sub_one,he]
    · intro e _ he; simpa using he
    · intro e _ he; exact he
    · simp
  · apply actual_masked_strong a b c (c+2) 3 3 (3 ^^^ wl.2) 0 v v wl.1
      ha (by omega) (by omega) (by omega)
    · simpa only [show c+2-1=c+1 by omega] using hcap
    · simpa only [show c+2-1=c+1 by omega] using hcap
    · simpa only [show c+2-1=c+1 by omega] using lt_of_le_of_lt hx.1 hcap
    · exact Nat.two_pow_pos _
    · exact hv.1
    · exact hv.1
    · exact hw.1
    · intro e _ he; exact he
    · intro e _ he; exact hbits e he
    · intro e _ he; exact he
    · simp
    · dsimp only
      have he : (2:ℤ)^(c+2-1)=2*(2:ℤ)^c := by
        rw [show c+2-1=c+1 by omega,pow_succ]; ring
      rw [he]
      simp only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,sub_zero,add_zero,zero_add]
      have hs : e1≤3*A ∧ 3*A≤2*e1-A ∧ e2≤S ∧ S≤2*e2-A ∧
          e3≤A*(3 ^^^ wl.2:ℕ)+2*e1*v+2*e2*wl.1 ∧
          A*(3 ^^^ wl.2:ℕ)+2*e1*v+2*e2*wl.1≤2*e3-A := by
        rw [hx.2]
        exact ⟨hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.2.1,hv.2.2.2.2.2.2.1,
          by dsimp [S] at hw; nlinarith only [hw.2.2.1],
          by dsimp [S] at hw; nlinarith only [hw.2.2.2]⟩
      dsimp only [A,e1,e2,e3,S,R,T,Z] at hs
      simp only [Nat.cast_pow,Nat.cast_ofNat] at hs
      ring_nf at hs ⊢
      exact hs

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
