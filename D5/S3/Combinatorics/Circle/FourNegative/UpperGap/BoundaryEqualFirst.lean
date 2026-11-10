/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryEqualFirst
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-equal-first-physical-construction)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Disjoint physical singleton masks and reordered packets when the first gaps agree. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryReordered
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private base newBase charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private reorderedMargins reordered_certificate
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryReordered
open private equal_first_small_endpoints equal_first_large_endpoints
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryAlgebra
open private qpow_four qpow_two qpow_one qpow_split qpow_half
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryMargins
open private singleton_capacity one_mask_capacity
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryConstruction
open private distinct_singletons_union
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.Rounding

set_option maxHeartbeats 1800000 in
private theorem equal_first_small_margins (a c : ℕ)
    (ha : 2≤a) (hac : a<c) (hsmall : c<2*a) :
    reorderedMargins a a c (c+1) 0 (2^(c-a-1)) := by
  have hp : (2:ℚ)^(c-a+1)≤2^a :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  rw [pow_succ] at hp
  have h := equal_first_small_endpoints (2^(c-a)) (2^a-2*2^(c-a)) 0
    (qpow_two _ (by omega)) (by linarith) (by norm_num)
  dsimp only at h
  have ex : (2:ℚ)^(c-a)*2+(2^a-2*2^(c-a))=2^a := by ring
  rw [ex,qpow_split c a (by omega),qpow_half (c-a) (by omega)] at h
  dsimp [reorderedMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify
  simp only [pow_succ] at h ⊢
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,_⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [v0]
  · nlinarith only [v1]
  · nlinarith only [v2]
  · nlinarith only [v3]
  · nlinarith only [v4]
  · nlinarith only [v5]
  · nlinarith only [v6]
  · nlinarith only [v7]
  · nlinarith only [v8]
  · nlinarith only [v9]
  · nlinarith only [v10]
  · nlinarith only [v11]

set_option maxHeartbeats 1800000 in
private theorem equal_first_large_margins (a c : ℕ)
    (ha : 2≤a) (hlarge : 2*a≤c) :
    reorderedMargins a a c (c+1) (2^(c-2*a)) (2^(c-a-1)) := by
  have h := equal_first_large_endpoints (2^a) (2^(c-2*a)) 0
    (qpow_four a ha) (qpow_one _) (by norm_num)
  dsimp only at h
  have ez : (2:ℚ)^a*2^a*2^(c-2*a)=2^c := by
    rw [←pow_add,←pow_add]
    congr 1
    omega
  have eq : (2:ℚ)^a*2^(c-2*a)/2=2^(c-a-1) := by
    rw [←pow_add,show a+(c-2*a)=c-a by omega,qpow_half (c-a) (by omega)]
  rw [ez,eq] at h
  dsimp [reorderedMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify
  simp only [pow_succ] at h ⊢
  obtain ⟨v0,v1,v2,v3,v4,v5,v6,v7,v8,v9,v10,v11,_⟩ := h
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [v0]
  · nlinarith only [v1]
  · nlinarith only [v2]
  · nlinarith only [v3]
  · nlinarith only [v4]
  · nlinarith only [v5]
  · nlinarith only [v6]
  · nlinarith only [v7]
  · nlinarith only [v8]
  · nlinarith only [v9]
  · nlinarith only [v10]
  · nlinarith only [v11]

private theorem equal_first_certificate (a c : ℕ) (ha : 2≤a) (hac : a<c) :
    Nonempty (Certificate a a c (c+1)) := by
  have hq : 2^(c-a-1)<2^(c-1) := singleton_capacity _ _ (by omega)
  by_cases hlarge : 2*a≤c
  · have hp : 2^(c-2*a)<2^(c-2) := singleton_capacity _ _ (by omega)
    have hq' : 2^(c-a-1)<2^(c-2) := singleton_capacity _ _ (by omega)
    have hsum : 2^(c-2*a)+2^(c-a-1)<2^(c-1) := by
      have he : (2:ℕ)^(c-1)=2^(c-2)*2 := by rw [show c-1=(c-2)+1 by omega,pow_succ]
      rw [he];omega
    have hor := distinct_singletons_union (c-2*a) (c-a-1) (by omega)
    apply reordered_certificate a a c (c+1) (2^(c-2*a)) (2^(c-a-1))
      ha ha (by omega) (by omega) (by simpa using one_mask_capacity c (by omega)) hsum hq
    · intro e _ he
      rw [←hor,Nat.testBit_or]
      simp [he]
    · exact equal_first_large_margins a c ha hlarge
  · apply reordered_certificate a a c (c+1) 0 (2^(c-a-1))
      ha ha (by omega) (by omega) (by simpa using one_mask_capacity c (by omega))
      (by simpa using hq) hq
    · intro e _ he;simpa using he
    · exact equal_first_small_margins a c ha hac (by omega)

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
