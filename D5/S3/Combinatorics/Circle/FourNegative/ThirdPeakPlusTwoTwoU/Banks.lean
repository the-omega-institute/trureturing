/- GID: D5/S3/Combinatorics/Circle/FourNegative/ThirdPeakPlusTwoTwoU/Banks
   generality: I
   mirror-B: none(waiver:private-consumed-implementation-described-at-endpoint)
   mirror-E: none(waiver:physical-dependent-source-registration-at-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Complementary physical banks and exact old and new packet masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint
import D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers.Masks

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (size negatives chainLength chainStart)

private def full (a b c d : ℕ) (r : Fin 4) : ℕ := 2^(chainLength a b c d r-1)-1
private def stock (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c d r-1) (chainStart b c d r) mask
private def complement (a b c d : ℕ) (r : Fin 4) (mask : ℕ) : List ℕ :=
  stock a b c d r (full a b c d r ^^^ mask)
private def terminals (a b c d : ℕ) : Fin 4→ℕ :=
  ![d+c+b-1,d+c-1,a+b+c+d-1,d-1]
private def banks (a b c d u v : ℕ) : Fin 4→List ℕ :=
  ![complement a b c d 0 u,stock a b c d 3 (full a b c d 3),
    stock a b c d 2 (full a b c d 2)++stock a b c d 1 v,
    stock a b c d 0 u++complement a b c d 1 v]
private def pre (a b c d u v : ℕ) : List ℕ :=
  let P:=banks a b c d u v
  let T:=terminals a b c d
  P 0++[T 0]++P 1++[T 1]++P 2
private def post (a b c d u v : ℕ) : List ℕ :=
  let P:=banks a b c d u v
  let T:=terminals a b c d
  [T 2]++P 3++[T 3]
private def word (a b c d u v : ℕ) : List ℕ := pre a b c d u v++post a b c d u v
private def marked (a b c d u v : ℕ) : List ℕ :=
  pre a b c d u v++[size a b c d]++post a b c d u v

private theorem stock_split (a b c d : ℕ) (r : Fin 4) (mask : ℕ) :
    (complement a b c d r mask++stock a b c d r mask).Perm
      (stock a b c d r (full a b c d r)) := by
  apply chamberLabels_split
  intro e he _
  simp [full,Nat.testBit_two_pow_sub_one,he]

private theorem canonical_inventory (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
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
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (u v : ℕ) :
    (word a b c d u v).Perm (List.range (size a b c d)) := by
  have hs0:=Multiset.coe_eq_coe.mpr (stock_split a b c d 0 u)
  have hs1:=Multiset.coe_eq_coe.mpr (stock_split a b c d 1 v)
  simp only [←Multiset.coe_add] at hs0 hs1
  apply Multiset.coe_eq_coe.mp
  change (word a b c d u v : Multiset ℕ)=(List.range (a+b+c+d) : Multiset ℕ)
  rw [←canonical_inventory a b c d ha hb hc hd]
  simp only [←Multiset.coe_add,Multiset.coe_singleton,←Multiset.cons_coe,←Multiset.singleton_add]
  rw [←hs0,←hs1]
  dsimp [word,pre,post,banks,terminals]
  simp only [←Multiset.coe_add,Multiset.coe_singleton,←Multiset.cons_coe,←Multiset.singleton_add]
  ac_rfl

private theorem banks_good (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (u v : ℕ) (r : Fin 4) (i : ℕ) (hi : i∈banks a b c d u v r) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have good (s : Fin 4) (mask : ℕ) (h : i∈stock a b c d s mask) :
      i<size a b c d ∧ i∉negatives a b c d := by
    obtain ⟨e,he,_,rfl⟩ := (chamberLabels_mem _ _ _ _).mp h
    fin_cases s <;> simp [chainLength,chainStart] at he ⊢
    all_goals simp only [size,negatives,List.mem_cons,List.mem_nil_iff,or_false]
    all_goals omega
  fin_cases r <;> dsimp [banks,complement] at hi
  all_goals try (simp only [List.mem_append] at hi; rcases hi with hi|hi)
  all_goals exact good _ _ hi

private theorem banks_masses (a b c d u v : ℕ)
    (hu : u<2^(d-1)) (hv : v<2^(c-1))
    (f : ℕ→ℤ) (F : Fin 4→ℤ)
    (hf : ∀ r : Fin 4, ∀ e<chainLength a b c d r-1,
      f (chainStart b c d r+e)=2^e*F r) :
    let C:=fun r : Fin 4 => (full a b c d r:ℤ)
    (fun r => ((banks a b c d u v r).map f).sum)=
      ![(C 0-u)*F 0,C 3*F 3,C 2*F 2+v*F 1,u*F 0+(C 1-v)*F 1] := by
  dsimp only
  have hfull (r : Fin 4) : full a b c d r<2^(chainLength a b c d r-1) := by
    dsimp [full]; have := Nat.two_pow_pos (chainLength a b c d r-1); omega
  have mass (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :
      ((stock a b c d r m).map f).sum=(m:ℤ)*F r :=
    chamberLabels_sum _ _ _ hm f (F r) (hf r)
  have comp (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c d r-1)) :
      ((complement a b c d r m).map f).sum=((full a b c d r:ℤ)-m)*F r := by
    have hs := ((stock_split a b c d r m).map f).sum_eq
    simp only [List.map_append,List.sum_append] at hs
    rw [mass r m hm,mass r _ (hfull r)] at hs
    linarith only [hs]
  have hu' : u<2^(chainLength a b c d 0-1) := by simpa [chainLength] using hu
  have hv' : v<2^(chainLength a b c d 1-1) := by simpa [chainLength] using hv
  have mU:=mass 0 u hu'
  have mV:=mass 1 v hv'
  have mW:=mass 2 _ (hfull 2)
  have mX:=mass 3 _ (hfull 3)
  have nU:=comp 0 u hu'
  have nV:=comp 1 v hv'
  funext r
  fin_cases r <;> dsimp [banks]
  all_goals simp only [List.map_append,List.sum_append,mU,mV,mW,mX,nU,nV]

end D5.S3.Combinatorics.Circle.FourNegative.ThirdPeakPlusTwoTwoU
