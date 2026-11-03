/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Masks
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Masks and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.Large

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative

theorem pow_two_mod_five (s : ℕ) :
    2^s%5=1 ∨ 2^s%5=2 ∨ 2^s%5=4 ∨ 2^s%5=3 := by
  induction s with
  | zero => norm_num
  | succ s ih =>
    rw [pow_succ,Nat.mul_mod]
    rcases ih with h|h|h|h <;> rw [h] <;> norm_num

theorem dyadic_eight (s : ℕ) (hs : 64≤2^s) : 2^s%8=0 := by
  have hs3 : 3≤s := by
    by_contra h
    interval_cases s <;> norm_num at hs
  obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le hs3
  rw [pow_add]
  norm_num [Nat.mul_mod]

theorem dyadic_large_partition (s : ℕ) (hs : 2≤2^s) :
    2^s=2 ∨ 2^s=4 ∨ 2^s=8 ∨ 16≤2^s := by
  by_cases h : 4≤s
  · right; right; right
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) h)
  · interval_cases s <;> norm_num at hs <;> norm_num

theorem dyadic_small_partition (s : ℕ) (hs : 2≤2^s) (hsmall : 2^s<64) :
    2^s=2 ∨ 2^s=4 ∨ 2^s=8 ∨ 2^s=16 ∨ 2^s=32 := by
  have h : s<6 := by
    by_contra hn
    have := Nat.pow_le_pow_right (n:=2) (by decide) (show 6≤s by omega)
    norm_num at this
    omega
  interval_cases s <;> norm_num at hs <;> norm_num

theorem dyadic_p_partition (s : ℕ) (hs : 4≤2^s) :
    2^s=4 ∨ 2^s=8 ∨ 2^s=16 ∨ 2^s=32 ∨ 64≤2^s := by
  by_cases h : 6≤s
  · right; right; right; right
    exact le_trans (by norm_num) (Nat.pow_le_pow_right (by decide) h)
  · interval_cases s <;> norm_num at hs <;> norm_num

private theorem submask_six (M : ℕ) (hM : M%8=6 ∨ M%8=7) :
    SecondPeakHighD.Submask 6 M := by
  have hm : M=2^3*(M/8)+M%8 := by norm_num; omega
  rw [hm]
  apply SecondPeakHighD.submask_high_block 3 (M/8) (M%8) 6
  · omega
  · norm_num
  · rcases hM with h|h <;> rw [h] <;>
      exact SecondPeakHighD.submask_of_land _ _ (by decide)

/-- The finite residue table is a Presburger proof for arbitrary q, not a grid. -/
theorem small_delta (p q : ℕ)
    (hp : p=4 ∨ p=8 ∨ p=16 ∨ p=32) (hq : 64≤q)
    (hq8 : q%8=0) (hq5 : q%5≠0) (hex : p=4 → q%5≠1) :
    ∃ delta : ℕ, 2≤delta ∧ delta≤4*p ∧
      (8*p*(q-1)+delta)%5=0 ∧
      ((8*p*(q-1)+delta)/5%8=6 ∨ (8*p*(q-1)+delta)/5%8=7) := by
  have hr : q%5=1 ∨ q%5=2 ∨ q%5=3 ∨ q%5=4 := by omega
  rcases hp with rfl|rfl|rfl|rfl <;> rcases hr with hr|hr|hr|hr
  · exact False.elim (hex rfl hr)
  · exact ⟨3,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨6,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨14,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨30,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨6,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨22,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨3,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨30,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨22,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨14,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨6,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨30,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨14,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨38,by norm_num,by norm_num,by omega,by omega⟩
  · exact ⟨22,by norm_num,by norm_num,by omega,by omega⟩

/-- Exact odd rounding for h=2. -/
theorem odd_mask (p q : ℕ) (hp : 4≤p) (hq : 64≤q) :
    ∃ M : ℕ, 1<M ∧ SecondPeakHighD.Submask 1 M ∧
      (4≤5*(M:ℤ)-(y p q 2-16*(p:ℤ))) ∧
      (5*(M:ℤ)-(y p q 2-16*(p:ℤ))<14) := by
  let w := 16*p*(q-1)
  let n := (w+18)/10
  let M := 2*n-1
  have hw : 100≤w := by dsimp [w]; nlinarith [Nat.mul_le_mul hp (show 63≤q-1 by omega)]
  have hn : 1≤n := by dsimp [n]; omega
  have heq : (w:ℤ)=y p q 2-16*(p:ℤ) := by
    dsimp [w,y]
    push_cast [Nat.cast_sub (by omega : 1≤q)]
    ring
  refine ⟨M,by dsimp [M,n]; omega,?_,?_,?_⟩
  · exact SecondPeakHighD.submask_predecessor 1 n 1 hn (by norm_num)
  · rw [←heq]
    dsimp [M,n]
    omega
  · rw [←heq]
    dsimp [M,n]
    omega

/-- The high/low exceptional mask is proved for every dyadic q in this sector. -/
theorem exceptional_mask (s : ℕ) (hq : 64≤2^s) (hr : 2^s%5=1) :
    let q : ℕ := 2^s
    let m : ℕ := 2*q+1
    let M : ℕ := (32*q-27)/5
    m<M ∧ SecondPeakHighD.Submask m M ∧
      5*(M:ℤ)-(y 4 q 1-32)=5 := by
  dsimp only
  let q : ℕ := 2^s
  let r := (2*q-27)/5
  let M : ℕ := (32*q-27)/5
  have hqpos : 0<q := by dsimp [q]; positivity
  have heq : M=6*q+r := by dsimp [M,r,q]; omega
  have hrlo : 0<r := by dsimp [r,q]; omega
  have hrhi : r<q := by dsimp [r,q]; omega
  have hrodd : r%2=1 := by dsimp [r,q]; omega
  have hp : 2^(s+1)=2*q := by dsimp [q]; rw [pow_succ]; ring
  have hbits : 2*q+1=2^(s+1) ||| 2^0 := by
    have hsmall : 1<(2:ℕ)^(s+1) := by rw [hp]; omega
    calc
      2*q+1=1+2^(s+1) := by rw [hp]; omega
      _=1 ||| 2^(s+1) := (Nat.or_two_pow_eq_add_of_lt hsmall).symm
      _=2^(s+1) ||| 2^0 := by norm_num [Nat.or_comm]
  change 2*q+1<M ∧ SecondPeakHighD.Submask (2*q+1) M ∧
    5*(M:ℤ)-(y 4 q 1-32)=5
  refine ⟨by dsimp [M,q]; omega,?_,?_⟩
  · intro e he
    change (2*q+1).testBit e=true at he
    change M.testBit e=true
    rw [hbits,Nat.testBit_or] at he
    simp only [Nat.testBit_two_pow,Bool.or_eq_true,decide_eq_true_eq] at he
    rcases he with he|he
    · subst e
      have hdiv : (6*q+r)/(2*q)=3 := by
        apply Nat.div_eq_of_lt_le <;> omega
      change M.testBit (s+1)=true
      simp [Nat.testBit,Nat.shiftRight_eq_div_pow,hp,heq,hdiv]
    · subst e
      have hodd : M%2^1=1 := by norm_num; rw [heq]; omega
      have ht := Nat.testBit_mod_two_pow M 1 0
      rw [hodd] at ht
      simpa using ht.symm
  · have hq64 : 64≤q := hq
    have hME : 5*M=32*q-27 := by dsimp [M,q]; omega
    have hi : (5:ℤ)*(M:ℤ)=32*(q:ℤ)-27 := by omega
    dsimp [y]
    omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
