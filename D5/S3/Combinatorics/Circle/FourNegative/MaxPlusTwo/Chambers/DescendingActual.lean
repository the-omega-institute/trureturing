/- GID: D5/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/DescendingActual
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/MaxPlusTwo/Chambers/DescendingActual
   mirror-E: none(waiver:internal-source-bridge)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Actual physical descending inventories and exact-charge Strong seams. -/
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.DescendingMasks

/-! The descending reserves act on the literal physical blocks. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private seedZ old charge from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Lift
open private Strong from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Strip
open private masked_inventory from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualBlocks
open private actual_masked_strong_exact
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.ActualStrong
open private descending_masks descending_word
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.DescendingMasks

set_option maxHeartbeats 1000000 in
private theorem descending_actual (a b c : ℕ) (hc : 2≤c) (hcb : c≤b) (hba : b≤a)
    (hedge : ¬((2:ℕ)^c=4 ∧ (2:ℕ)^a=2*2^b)) :
    (baseWord a b c).Perm (List.range (a+b+c+(a+2))) ∧
      Strong (old a b c (a+2)) (charge a b c (a+2))
        (2^(a+2-1)*2^a*2^b*2^c) 0 (seedZ a b c) (baseWord a b c) := by
  let R : ℕ:=2^a
  let T : ℕ:=2^b
  let Z : ℕ:=2^c
  let u1:=(2*R/Z) ||| (2*R/T) ||| 2
  let u2:=(2*R/T) ||| 2
  obtain ⟨hu1,hu2,hu3,h12,h23,hs⟩:=descending_masks a b c hc hcb hba hedge
  change u1<2^(a+1) at hu1
  change u2<2^(a+1) at hu2
  change ∀ e, u2.testBit e=true → u1.testBit e=true at h12
  change ∀ e, (2:ℕ).testBit e=true → u2.testBit e=true at h23
  rw [descending_word a b c hcb hba hedge]
  constructor
  · apply masked_inventory a b c (a+2) u1 u2 2 0 0 0 0
      (by omega) (by omega) (by omega) (by omega)
    · intro e _ he; exact h12 e he
    · intro e _ he; exact h23 e he
    · intro e he _; simp [Nat.testBit_two_pow_sub_one,he]
    · simp
    · simp
    · simp
  · apply actual_masked_strong_exact a b c (a+2) u1 u2 2 0 0 0 0
      (by omega) (by omega) hc (by omega)
    · simpa only [show a+2-1=a+1 by omega] using hu1
    · simpa only [show a+2-1=a+1 by omega] using hu2
    · simpa only [show a+2-1=a+1 by omega] using hu3
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · exact Nat.two_pow_pos _
    · intro e _ he; exact h12 e he
    · intro e _ he; exact h23 e he
    · simp
    · simp
    · dsimp only
      have he : (2:ℤ)^(a+2-1)=2*(2:ℤ)^a := by
        rw [show a+2-1=a+1 by omega,pow_succ]; ring
      rw [he]
      simp only [Nat.cast_zero,Nat.cast_ofNat,mul_zero,sub_zero,add_zero,zero_add]
      dsimp only [u1,u2,R,T,Z]
      simp only [Nat.cast_pow,Nat.cast_ofNat] at hs
      ring_nf at hs ⊢
      exact hs

end D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
