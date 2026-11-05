/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Dilation
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Dyadic dilation preserves actual nested bit supports and their complements. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks

/-! Actual bit supports for the dyadic reserved-bank construction. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open scoped BigOperators
open private scaled_bits full_bits from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks

private def dilation (s m : ℕ) : ℕ := 2^s*m+(2^s-1)
private def Submask (j m : ℕ) : Prop := j.bitIndices.toFinset ⊆ m.bitIndices.toFinset

private theorem dilation_eq (s m : ℕ) : dilation s m=2^s*(m+1)-1 := by
  have hp := Nat.two_pow_pos s
  dsimp [dilation]
  rw [Nat.mul_add,Nat.mul_one]
  omega

private theorem dilation_bits (s m : ℕ) :
    (dilation s m).bitIndices.toFinset=
      m.bitIndices.toFinset.image (s+·) ∪ Finset.range s := by
  classical
  have hd : Disjoint (m.bitIndices.toFinset.image (s+·)) (Finset.range s) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hi
    have := Finset.mem_range.mp hj
    omega
  apply Finset.geomSum_injective (by decide : 2 ≤ (2:ℕ))
  dsimp only
  rw [Finset.sum_toFinset_bitIndices_two_pow,Finset.sum_union hd,
    ←scaled_bits s m,←full_bits s]
  simp only [Finset.sum_toFinset_bitIndices_two_pow]
  rfl

private theorem dilation_submask (s j m : ℕ) (hj : Submask j m) :
    Submask (dilation s j) (dilation s m) := by
  dsimp [Submask] at *
  rw [dilation_bits,dilation_bits]
  exact Finset.union_subset_union (Finset.image_mono (s+·) hj) (Finset.Subset.refl _)

private theorem submask_xor (j m : ℕ) (hj : Submask j m) :
    (m ^^^ j)+j=m := by
  classical
  have hs (i : ℕ) : j.testBit i=true → m.testBit i=true := by
    intro hi
    have hm := hj (by simpa using Nat.mem_bitIndices.mpr hi)
    simpa using hm
  have hu : (m ^^^ j).bitIndices.toFinset ∪ j.bitIndices.toFinset=m.bitIndices.toFinset := by
    ext i
    simp only [Finset.mem_union,List.mem_toFinset,Nat.mem_bitIndices,Nat.testBit_xor]
    have h := hs i
    cases hm : m.testBit i <;> cases hh : j.testBit i <;> simp_all
  have hd : Disjoint (m ^^^ j).bitIndices.toFinset j.bitIndices.toFinset := by
    apply Finset.disjoint_left.mpr
    intro i hi hj'
    have hb : j.testBit i=true := by simpa using hj'
    have hm := hs i hb
    simpa [Nat.testBit_xor,hm,hb] using hi
  have h := Finset.sum_union hd (f:=fun i : ℕ => 2^i)
  rw [hu] at h
  simpa only [Finset.sum_toFinset_bitIndices_two_pow] using h.symm

private theorem dilation_xor (s j m : ℕ) (hj : Submask j m) :
    dilation s m ^^^ dilation s j=2^s*(m ^^^ j) := by
  have h0 := submask_xor j m hj
  have h1 := submask_xor _ _ (dilation_submask s j m hj)
  dsimp [dilation] at h1 ⊢
  have h2 := congrArg (fun n => 2^s*n) h0
  rw [Nat.mul_add] at h2
  omega

private theorem dilation_cap (s c m : ℕ) (hm : m<2^c) :
    dilation s m<2^(c+s) := by
  calc
    dilation s m=2^s*m+(2^s-1) := rfl
    _ < 2^s*m+2^s := Nat.add_lt_add_left (Nat.sub_lt (Nat.two_pow_pos s) (by decide)) _
    _ = 2^s*(m+1) := by ring
    _ ≤ 2^s*2^c := Nat.mul_le_mul_left _ (by omega)
    _ = 2^(c+s) := by rw [pow_add]; exact Nat.mul_comm _ _

private theorem full_submask (c m : ℕ) (hm : m<2^c) : Submask m (2^c-1) := by
  dsimp [Submask]
  rw [full_bits]
  intro i hi
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  apply Finset.mem_range.mpr
  by_contra hn
  have hh := Nat.pow_le_pow_right (by decide : 0<2) (show c ≤ i by omega)
  omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
