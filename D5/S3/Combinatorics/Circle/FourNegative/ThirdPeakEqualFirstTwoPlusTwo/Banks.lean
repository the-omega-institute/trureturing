/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakEqualFirstTwoPlusTwo/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact physical stocks and paired source masses for the equal-first-two plus-two allocation. -/
import D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo.Parameters

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size negatives chainLength chainStart)

private def full (a b c d : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c d r-1)-1
private def stock (a b c d : ℕ) (r : Fin 4) (m : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) m
private def complement (a b c d : ℕ) (r : Fin 4) (m : ℕ) : List ℕ :=
  stock a b c d r (full a b c d r ^^^ m)
private def terminals (a b c d : ℕ) : Fin 4→ℕ :=
  ![d+c-1,d+c+b-1,a+b+c+d-1,d-1]
private def banks (a b c d u v : ℕ) : Fin 4→List ℕ :=
  ![complement a b c d 0 u,stock a b c d 2 (full a b c d 2),
    stock a b c d 3 (full a b c d 3)++stock a b c d 1 v,
    stock a b c d 0 u++complement a b c d 1 v]
private def word (a b c d u v : ℕ) : List ℕ :=
  let P:=banks a b c d u v
  let Z:=terminals a b c d
  P 0++[Z 0]++P 1++[Z 1]++P 2++[Z 2]++P 3++[Z 3]

private theorem stock_split (a b c d : ℕ) (r : Fin 4) (m : ℕ) :
    (complement a b c d r m++stock a b c d r m).Perm
      (stock a b c d r (full a b c d r)) := by
  apply chamberLabels_split
  intro e he _
  simp [full,Nat.testBit_two_pow_sub_one,he]

private theorem canonical_inventory (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    stock a b c d 0 (full a b c d 0)++[d-1]++
      stock a b c d 1 (full a b c d 1)++[d+c-1]++
      stock a b c d 2 (full a b c d 2)++[d+c+b-1]++
      stock a b c d 3 (full a b c d 3)++[a+b+c+d-1]=List.range (a+b+c+d) := by
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
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (u v : ℕ) :
    (word a b c d u v).Perm (List.range (a+b+c+d)) := by
  have hs0:=Multiset.coe_eq_coe.mpr (stock_split a b c d 0 u)
  have hs1:=Multiset.coe_eq_coe.mpr (stock_split a b c d 1 v)
  simp only [←Multiset.coe_add] at hs0 hs1
  apply Multiset.coe_eq_coe.mp
  rw [←canonical_inventory a b c d ha hb hc hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  rw [←hs0,←hs1]
  dsimp [word,banks,terminals]
  simp only [←Multiset.coe_add,Multiset.coe_singleton]
  ac_rfl

private theorem stock_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (r : Fin 4) (m i : ℕ) (hi : i∈stock a b c d r m) :
    i<size a b c d ∧ i∉negatives a b c d := by
  obtain ⟨e,he,_,rfl⟩:=(chamberLabels_mem _ _ _ _).mp hi
  fin_cases r <;> simp [chainLength,chainStart] at he ⊢
  all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
  all_goals omega

private theorem banks_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (u v : ℕ) (r : Fin 4) (i : ℕ) (hi : i∈banks a b c d u v r) :
    i<size a b c d ∧ i∉negatives a b c d := by
  fin_cases r <;> dsimp [banks,complement] at hi
  all_goals try (simp only [List.mem_append] at hi; rcases hi with hi|hi)
  all_goals exact stock_good a b c d ha hb hc hd _ _ i hi

private theorem stock_mass (a b c d : ℕ) (r : Fin 4) (m : ℕ)
    (hm : m<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((stock a b c d r m).map f).sum=(m:ℤ)*F r := by
  exact chamberLabels_sum _ _ _ hm f (F r) (hf r)

private theorem complement_mass (a b c d : ℕ) (r : Fin 4) (m : ℕ)
    (hm : m<2^(chainLength a b c d r-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    ((complement a b c d r m).map f).sum=((full a b c d r:ℤ)-(m:ℤ))*F r := by
  have hfull : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have hs:=((stock_split a b c d r m).map f).sum_eq
  simp only [List.map_append,List.sum_append] at hs
  rw [stock_mass a b c d r m hm f F hf,stock_mass a b c d r _ hfull f F hf] at hs
  linarith only [hs]

private theorem banks_masses (a b c d u v : ℕ)
    (hu : u<2^(d-1)) (hv : v<2^(c-1)) (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c d r:ℤ)
    (fun r => ((banks a b c d u v r).map f).sum)=
      ![(C 0-u)*F 0,C 2*F 2,C 3*F 3+v*F 1,u*F 0+(C 1-v)*F 1] := by
  dsimp only
  have hu' : u<2^(chainLength a b c d 0-1) := by simpa [chainLength] using hu
  have hv' : v<2^(chainLength a b c d 1-1) := by simpa [chainLength] using hv
  have hfull (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have mU:=stock_mass a b c d 0 u hu' f F hf
  have mV:=stock_mass a b c d 1 v hv' f F hf
  have mW:=stock_mass a b c d 2 _ (hfull 2) f F hf
  have mX:=stock_mass a b c d 3 _ (hfull 3) f F hf
  have nU:=complement_mass a b c d 0 u hu' f F hf
  have nV:=complement_mass a b c d 1 v hv' f F hf
  funext r
  fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mU,mV,mW,mX,nU,nV]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakEqualFirstTwoPlusTwo
