/- GID: D5/S3/Combinatorics/Circle/FourNegative/UpperGap/BoundaryMargins
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:private-dyadic-chart-transport)
   anchors: [mathlib/module/Mathlib.Tactic.Qify]
   utility: none
   digest: Exact dyadic specialization of the boundary polynomial margins. -/
import D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets
import Mathlib.Tactic.Qify

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.UpperGap
open private base newBase charge
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private standardMargins
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryPackets
open private rising_endpoints swapped_endpoints tied_ac_endpoints all_equal_endpoints
  from D5.S3.Combinatorics.Circle.FourNegative.UpperGap.BoundaryAlgebra

private theorem qpow_four (n : ℕ) (hn : 2≤n) : (4:ℚ)≤2^n := by
  have h := pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) hn
  norm_num at h
  exact h
private theorem qpow_two (n : ℕ) (hn : 1≤n) : (2:ℚ)≤2^n := by
  simpa using pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) hn
private theorem qpow_one (n : ℕ) : (1:ℚ)≤2^n := by
  simpa using pow_le_pow_right₀ (by norm_num : (1:ℚ)≤2) (Nat.zero_le n)
private theorem qpow_split (n k : ℕ) (hk : k≤n) :
    (2:ℚ)^k*2^(n-k)=2^n := by rw [←pow_add,Nat.add_sub_of_le hk]
private theorem qpow_half (n : ℕ) (hn : 1≤n) :
    (2:ℚ)^n/2=2^(n-1) := by
  have h : (2:ℚ)^(n-1)*2=2^n := by rw [←pow_succ,Nat.sub_add_cancel hn]
  rw [←h]
  ring

set_option maxHeartbeats 1600000 in
private theorem rising_margins (a b c : ℕ) (ha : 2≤a) (hab : a<b) (hbc : b<c) :
    standardMargins a b c (c+1) 1 0 (2^(c-b)-1) 0 (2^(b-a-1)) := by
  have h := rising_endpoints (2^a) (2^(b-a)) (2^(c-b)) (qpow_four a ha) (qpow_two _ (by omega)) (qpow_two _ (by omega))
  dsimp only at h
  rw [qpow_split b a (by omega),qpow_split c b (by omega)] at h
  rw [qpow_half (b-a) (by omega)] at h
  dsimp [standardMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify [Nat.one_le_two_pow]
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

set_option maxHeartbeats 1600000 in
private theorem swapped_margins (a b c : ℕ) (hb : 2≤b) (hba : b<a) (hac : a<c) :
    standardMargins a b c (c+1) 1 1 (2^(c-b-1)-1) (2^(c-a-1)) 0 := by
  have h := swapped_endpoints (2^b) (2^(a-b)) (2^(c-a)) (qpow_four b hb) (qpow_two _ (by omega)) (qpow_two _ (by omega))
  dsimp only at h
  rw [qpow_split a b (by omega),qpow_split c a (by omega)] at h
  have ep : (2:ℚ)^(a-b)*2^(c-a)/2=2^(c-b-1) := by
    rw [←pow_add,show a-b+(c-a)=c-b by omega,qpow_half (c-b) (by omega)]
  rw [ep,qpow_half (c-a) (by omega)] at h
  dsimp [standardMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify [Nat.one_le_two_pow]
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

set_option maxHeartbeats 1600000 in
private theorem tied_margins (a b : ℕ) (hb : 2≤b) (hba : b<a) :
    standardMargins a b a (a+1) 1 1 (2^(a-b-1)-1) 0 0 := by
  have h := tied_ac_endpoints (2^b) (2^(a-b)) 0 (qpow_four b hb) (qpow_two _ (by omega)) (by norm_num)
  dsimp only at h
  rw [qpow_split a b (by omega),qpow_half (a-b) (by omega)] at h
  dsimp [standardMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify [Nat.one_le_two_pow]
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

set_option maxHeartbeats 1600000 in
private theorem all_equal_margins (a : ℕ) (ha : 2≤a) :
    standardMargins a a a (a+1) 0 0 0 0 0 := by
  have h := all_equal_endpoints (2^a) 0 0 (qpow_four a ha) (by norm_num) (by norm_num)
  dsimp only at h
  dsimp [standardMargins,base,newBase,charge]
  norm_num only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,Fin.isValue]
  qify [Nat.one_le_two_pow]
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

end D5.S3.Combinatorics.Circle.FourNegative.UpperGap
