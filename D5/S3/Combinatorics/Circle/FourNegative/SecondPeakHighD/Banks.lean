/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Banks
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Banks
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Banks and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private size negatives chainLength chainStart
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def full (a b c d : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c d r-1)-1
private def stock (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) mask
private def complement (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  stock a b c d r (full a b c d r ^^^ mask)
private def terminals (a b c d : ℕ) : Fin 4→ℕ :=
  ![a+b+c+d-1,d-1,d+c+b-1,d+c-1]
private def banks (a b c d v m M : ℕ) : Fin 4→List ℕ :=
  let s:=stock a b c d
  let f:=full a b c d
  let t:=complement a b c d
  ![s 3 (f 3)++s 0 (v-1)++s 2 m,
    t 0 (v-1)++s 2 (M ^^^ m),t 2 M,s 1 (f 1)]
private def word (a b c d v m M : ℕ) : List ℕ :=
  let P:=banks a b c d v m M
  let n:=terminals a b c d
  P 0++[n 0]++P 1++[n 1]++P 2++[n 2]++P 3++[n 3]

private theorem stock_split (a b c d : ℕ) (r : Fin 4) (mask : ℕ) :
    (complement a b c d r mask++stock a b c d r mask).Perm
      (stock a b c d r (full a b c d r)) := by
  apply chamberLabels_split
  intro e he _
  simp [full,Nat.testBit_two_pow_sub_one,he]

private theorem nested_split (a b c d m M : ℕ) (hs : Submask m M) :
    (stock a b c d 2 (M ^^^ m)++stock a b c d 2 m).Perm
      (stock a b c d 2 M) := by
  apply chamberLabels_split
  intro e _ he
  exact hs e he

private theorem canonical_inventory (a b c d : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    (stock a b c d 0 (full a b c d 0)++[d-1]++
      stock a b c d 1 (full a b c d 1)++[d+c-1]++
      stock a b c d 2 (full a b c d 2)++[d+c+b-1]++
      stock a b c d 3 (full a b c d 3)++[a+b+c+d-1])=List.range (a+b+c+d) := by
  simp only [stock,full,chamberLabels_full,chainLength,chainStart,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,
    Matrix.cons_val_zero',Matrix.cons_val_succ']
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1)++[off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega]
      using (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have h0:=merge 0 d (by omega)
  have h1:=merge d c (by omega)
  have h2:=merge (d+c) b (by omega)
  have h3:=merge (d+c+b) a (by omega)
  simp only [Nat.zero_add] at h0
  have h3' : List.range' (d+c+b) (a-1)++[a+b+c+d-1]=List.range' (d+c+b) a := by
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h3
  have join (m n : ℕ) : List.range' 0 m++List.range' m n=List.range' 0 (m+n) := by
    simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=m) (n:=n))
  calc
    _ = (List.range' 0 (d-1)++[d-1])++(List.range' d (c-1)++[d+c-1])++
        (List.range' (d+c) (b-1)++[d+c+b-1])++
        (List.range' (d+c+b) (a-1)++[a+b+c+d-1]) := by simp only [List.append_assoc]
    _ = List.range' 0 d++List.range' d c++List.range' (d+c) b++List.range' (d+c+b) a := by
      rw [h0,h1,h2,h3']
    _ = List.range (a+b+c+d) := by
      rw [join,join,join,←List.range_eq_range']
      congr 1
      omega


private theorem banks_inventory (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (v m M : ℕ) (hs : Submask m M) :
    (word a b c d v m M).Perm (List.range (a+b+c+d)) := by
  have hu:=Multiset.coe_eq_coe.mpr (stock_split a b c d 0 (v-1))
  have hw:=Multiset.coe_eq_coe.mpr (stock_split a b c d 2 M)
  have hn:=Multiset.coe_eq_coe.mpr (nested_split a b c d m M hs)
  simp only [←Multiset.coe_add] at hu hw hn
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c d ha hb hc hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hu,←hw,←hn]
  dsimp [word,banks,terminals]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  ac_rfl

private theorem stock_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (r : Fin 4) (mask i : ℕ) (hi : i∈stock a b c d r mask) :
    i<size a b c d ∧ i∉negatives a b c d := by
  obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;> simp [chainLength,chainStart] at he ⊢
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem banks_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (v m M : ℕ) (r : Fin 4) (i : ℕ) (hi : i∈banks a b c d v m M r) :
    i<size a b c d ∧ i∉negatives a b c d := by
  fin_cases r <;> dsimp [banks,complement] at hi
  all_goals try simp only [List.mem_append] at hi
  all_goals first
    | (rcases hi with (hi|hi)|hi)
    | (rcases hi with hi|hi)
    | skip
  all_goals exact stock_good a b c d ha hb hc hd _ _ i hi

private theorem stock_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((stock a b c d r mask).map f).sum=(mask:ℤ)*F r := by
  exact chamberLabels_sum _ _ _ hm f (F r) (hf r)

private theorem complement_mass (a b c d : ℕ) (r : Fin 4) (mask : ℕ)
    (hm : mask<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((complement a b c d r mask).map f).sum=((full a b c d r:ℕ)-(mask:ℤ))*F r := by
  have hfull : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c d r-1);omega
  have hs:=((stock_split a b c d r mask).map f).sum_eq
  simp only [List.map_append,List.sum_append] at hs
  rw [stock_mass a b c d r mask hm f F hf,stock_mass a b c d r _ hfull f F hf] at hs
  linarith only [hs]

private theorem banks_masses (a b c d v m M : ℕ)
    (hv0 : 1≤v) (hv : v≤2^(d-1)) (hM : M<2^(b-1)) (hs : Submask m M)
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c d r:ℤ)
    (fun r => (((banks a b c d v m M) r).map f).sum)=
      ![C 3*F 3+((v:ℤ)-1)*F 0+(m:ℤ)*F 2,
        (C 0-((v:ℤ)-1))*F 0+((M:ℤ)-(m:ℤ))*F 2,
        (C 2-(M:ℤ))*F 2,C 1*F 1] := by
  dsimp only
  have hm : m<2^(b-1) := lt_of_le_of_lt (submask_le m M hs) hM
  have hfull (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full];have := Nat.two_pow_pos (chainLength a b c d r-1);omega
  have huv : v-1<2^(chainLength a b c d 0-1) := by simpa [chainLength] using (show v-1<2^(d-1) by omega)
  have hMm : M<2^(chainLength a b c d 2-1) := by simpa [chainLength] using hM
  have hmm : m<2^(chainLength a b c d 2-1) := by simpa [chainLength] using hm
  have mX:=stock_mass a b c d 3 _ (hfull 3) f F hf
  have mU:=stock_mass a b c d 0 (v-1) huv f F hf
  have mW:=stock_mass a b c d 2 m hmm f F hf
  have mV:=stock_mass a b c d 1 _ (hfull 1) f F hf
  have nU:=complement_mass a b c d 0 (v-1) huv f F hf
  have nW:=complement_mass a b c d 2 M hMm f F hf
  have split:=((nested_split a b c d m M hs).map f).sum_eq
  simp only [List.map_append,List.sum_append] at split
  rw [mW,stock_mass a b c d 2 M hMm f F hf] at split
  have mMW : ((stock a b c d 2 (M ^^^ m)).map f).sum=((M:ℤ)-(m:ℤ))*F 2 := by
    linarith only [split]
  have hvcast : ((v-1:ℕ):ℤ)=(v:ℤ)-1 := by omega
  rw [hvcast] at mU nU
  funext r
  fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mX,mU,mW,mV,nU,nW,mMW]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
