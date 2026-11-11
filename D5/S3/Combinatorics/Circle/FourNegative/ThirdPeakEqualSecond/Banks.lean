/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualSecond/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-physical-banks)
   mirror-E: none(waiver:private-consumed-physical-banks)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Literal complementary physical inventories for the two equal-second schedules. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

/-! Masks select actual occurrences in the four original disjoint intervals. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size negatives chainLength chainStart)

private def full (a b c : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c b r-1)-1
private def stock (a b c : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c b r-1) (chainStart b c b r) mask
private def complement (a b c : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  stock a b c r (full a b c r ^^^ mask)
private def terminals (a b c : ℕ) (paid : Bool) : Fin 4→ℕ :=
  let t := ![b-1,b+c-1,b+c+b-1,a+b+c+b-1]
  if paid then t else ![t 1,t 2,t 3,t 0]
private def banks (a b c : ℕ) (paid : Bool) (v w q : ℕ) : Fin 4→List ℕ :=
  let s:=stock a b c
  let t:=complement a b c
  if paid then
    ![s 0 (full a b c 0)++s 1 v,t 1 v,t 2 w++s 3 q,s 2 w++t 3 q]
  else
    ![t 1 v,t 2 w,s 2 w++s 3 (full a b c 3),s 0 (full a b c 0)++s 1 v]
private def word (a b c : ℕ) (paid : Bool) (v w q : ℕ) : List ℕ :=
  let P:=banks a b c paid v w q
  let T:=terminals a b c paid
  P 0++[T 0]++P 1++[T 1]++P 2++[T 2]++P 3++[T 3]

private theorem stock_split (a b c : ℕ) (r : Fin 4) (mask : ℕ) :
    (complement a b c r mask++stock a b c r mask).Perm
      (stock a b c r (full a b c r)) := by
  apply chamberLabels_split
  intro e he _
  simp [full,Nat.testBit_two_pow_sub_one,he]

private theorem canonical_inventory (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    (stock a b c 0 (full a b c 0)++[b-1]++
      stock a b c 1 (full a b c 1)++[b+c-1]++
      stock a b c 2 (full a b c 2)++[b+c+b-1]++
      stock a b c 3 (full a b c 3)++[a+b+c+b-1])=List.range (a+b+c+b) := by
  simp only [stock,full,chamberLabels_full,chainLength,chainStart,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1)++[off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0:=merge 0 b (by omega)
  have h1:=merge b c (by omega)
  have h2:=merge (b+c) b (by omega)
  have h3:=merge (b+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have h3' : List.range' (b+c+b) (a-1)++[a+b+c+b-1]=List.range' (b+c+b) a := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h3
  have join (m n : ℕ) : List.range' 0 m++List.range' m n=List.range' 0 (m+n) := by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=m) (n:=n))
  calc
    _ = (List.range' 0 (b-1)++[b-1])++(List.range' b (c-1)++[b+c-1])++
        (List.range' (b+c) (b-1)++[b+c+b-1])++
        (List.range' (b+c+b) (a-1)++[a+b+c+b-1]) := by simp only [List.append_assoc]
    _ = List.range' 0 b++List.range' b c++List.range' (b+c) b++List.range' (b+c+b) a := by
      rw [h0,h1,h2,h3']
    _ = List.range (a+b+c+b) := by
      rw [join,join,join,←List.range_eq_range']
      congr 1
      omega

private theorem banks_inventory (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (paid : Bool) (v w q : ℕ) : (word a b c paid v w q).Perm (List.range (a+b+c+b)) := by
  have hs1:=Multiset.coe_eq_coe.mpr (stock_split a b c 1 v)
  have hs2:=Multiset.coe_eq_coe.mpr (stock_split a b c 2 w)
  have hs3:=Multiset.coe_eq_coe.mpr (stock_split a b c 3 q)
  simp only [←Multiset.coe_add] at hs1 hs2 hs3
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c ha hb hc]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  cases paid
  · rw [←hs1,←hs2]
    dsimp [word,banks,terminals]
    simp only [←Multiset.coe_add,Multiset.coe_singleton]
    ac_rfl
  · rw [←hs1,←hs2,←hs3]
    dsimp [word,banks,terminals]
    simp only [←Multiset.coe_add,Multiset.coe_singleton]
    ac_rfl

private theorem stock_good (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (r : Fin 4) (mask i : ℕ) (hi : i∈stock a b c r mask) :
    i<size a b c b ∧ i∉negatives a b c b := by
  obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;> simp [chainLength,chainStart] at he ⊢
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem banks_good (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (paid : Bool) (v w q : ℕ) (r : Fin 4) (i : ℕ) (hi : i∈banks a b c paid v w q r) :
    i<size a b c b ∧ i∉negatives a b c b := by
  cases paid <;> fin_cases r <;> dsimp [banks,complement] at hi
  all_goals try (simp only [List.mem_append] at hi; rcases hi with hi|hi)
  all_goals exact stock_good a b c ha hb hc _ _ i hi

private theorem stock_mass (a b c : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c b r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c b r-1,
      f (chainStart b c b r+e)=2^e*F r) :
    ((stock a b c r mask).map f).sum=(mask:ℤ)*F r := by
  exact chamberLabels_sum _ _ _ hm f (F r) (hf r)

private theorem complement_mass (a b c : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c b r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c b r-1,
      f (chainStart b c b r+e)=2^e*F r) :
    ((complement a b c r mask).map f).sum=((full a b c r:ℕ)-(mask:ℤ))*F r := by
  have hfull : full a b c r<2^(chainLength a b c b r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c b r-1);omega
  have hs:=((stock_split a b c r mask).map f).sum_eq
  simp only [List.map_append,List.sum_append] at hs
  rw [stock_mass a b c r mask hm f F hf,stock_mass a b c r _ hfull f F hf] at hs
  linarith only [hs]

private theorem banks_masses (a b c : ℕ) (paid : Bool) (v w q : ℕ)
    (hv : v<2^(c-1)) (hw : w<2^(b-1)) (hq : q<2^(a-1))
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c b r-1,
      f (chainStart b c b r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c r:ℤ)
    let P:=banks a b c paid v w q
    (fun r => ((P r).map f).sum)=
    if paid then ![C 0*F 0+v*F 1,(C 1-v)*F 1,
      (C 2-w)*F 2+q*F 3,w*F 2+(C 3-q)*F 3]
    else ![(C 1-v)*F 1,(C 2-w)*F 2,w*F 2+C 3*F 3,C 0*F 0+v*F 1] := by
  dsimp only
  have hv' : v<2^(chainLength a b c b 1-1) := by simpa [chainLength] using hv
  have hw' : w<2^(chainLength a b c b 2-1) := by simpa [chainLength] using hw
  have hq' : q<2^(chainLength a b c b 3-1) := by simpa [chainLength] using hq
  have hfull (r : Fin 4) : full a b c r<2^(chainLength a b c b r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c b r-1);omega
  have mU:=stock_mass a b c 0 _ (hfull 0) f F hf
  have mV:=stock_mass a b c 1 v hv' f F hf
  have mW:=stock_mass a b c 2 w hw' f F hf
  have mX:=stock_mass a b c 3 q hq' f F hf
  have mXF:=stock_mass a b c 3 _ (hfull 3) f F hf
  have nV:=complement_mass a b c 1 v hv' f F hf
  have nW:=complement_mass a b c 2 w hw' f F hf
  have nX:=complement_mass a b c 3 q hq' f F hf
  funext r
  cases paid <;> fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mU,mV,mW,mX,mXF,nV,nW,nX]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualSecond
