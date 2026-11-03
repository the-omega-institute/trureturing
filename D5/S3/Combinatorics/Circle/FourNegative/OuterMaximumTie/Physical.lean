/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Physical
   generality: I
   mirror-B: none(waiver:consumed-physical-banks)
   mirror-E: none(waiver:consumed-physical-banks)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Physical masks, complementary inventories and paired source masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Allocation
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.AscendingSource

/-! Complements are written as (2^len-1)-mask. The reused bit-partition
lemma proves their exact physical complement, without replacing occurrences
by equal values. In particular W(1) is the physical singleton [a+c]. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private low_split
  from D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.AscendingSource
open private size sourceMod base newBase charge chainLength chainStart oldValue newValue
  negatives chain_values
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def cap (len : ℕ) : ℕ := 2^(len-1)-1
private def C (a b c : ℕ) (r : Fin 4) (m : ℕ) : List ℕ :=
  chamberLabels (chainLength a b c a r-1) (chainStart b c a r) m
private def full (a b c : ℕ) (r : Fin 4) : List ℕ :=
  C a b c r (cap (chainLength a b c a r))
private def bank (asc : Bool) (a b c v w : ℕ) : Fin 4 → List ℕ :=
  if asc then ![full a b c 3,C a b c 0 (cap a-v),C a b c 1 (cap c-w),
    full a b c 2 ++ C a b c 0 v ++ C a b c 1 w]
  else ![full a b c 3,full a b c 1 ++ C a b c 0 v ++ C a b c 2 w,
    C a b c 0 (cap a-v),C a b c 2 (cap b-w)]
private def terminal (asc : Bool) (a b c : ℕ) : Fin 4 → ℕ :=
  if asc then ![a+b+c+a-1,a-1,a+c-1,a+c+b-1]
  else ![a+b+c+a-1,a+c-1,a-1,a+c+b-1]
private def word (asc : Bool) (a b c v w : ℕ) : List ℕ :=
  let P := bank asc a b c v w
  let T := terminal asc a b c
  P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]

private theorem complement_stock (len m : ℕ) (hm : m<2^(len-1)) :
    m≤cap len ∧ cap len-m<2^(len-1) := by
  have hp := Nat.two_pow_pos (len-1)
  dsimp [cap]; omega

private theorem complement_inventory (len off m : ℕ) (hm : m<2^len) :
    (chamberLabels len off (2^len-1-m) ++ chamberLabels len off m).Perm
      (List.range' off len) := by
  have h := low_split len off (m+1) (by omega) (by omega)
  have h0 : 2^len-(m+1)=2^len-1-m := by omega
  simpa only [h0,Nat.add_sub_cancel] using h

private theorem all_chains (a b c : ℕ) (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) :
    full a b c 0 ++ [a-1] ++ full a b c 1 ++ [a+c-1] ++
      full a b c 2 ++ [a+c+b-1] ++ full a b c 3 ++ [a+b+c+a-1]=
      List.range (a+b+c+a) := by
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,
      show len-1+1=len by omega] using
      (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have hall :
      (List.range' 0 (a-1) ++ [a-1]) ++
      (List.range' a (c-1) ++ [a+c-1]) ++
      (List.range' (a+c) (b-1) ++ [a+c+b-1]) ++
      (List.range' (a+c+b) (a-1) ++ [a+b+c+a-1])=List.range (a+b+c+a) := by
    have h0 := merge 0 a (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge a c (by omega),merge (a+c) b (by omega)]
    rw [show a+b+c+a-1=(a+c+b)+a-1 by omega,merge (a+c+b) a (by omega)]
    have hdc : List.range' 0 a ++ List.range' a c=List.range' 0 (a+c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=a) (n:=c))
    have hdcb : List.range' 0 (a+c) ++ List.range' (a+c) b=List.range' 0 (a+c+b) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=a+c) (n:=b))
    have hdcba : List.range' 0 (a+c+b) ++ List.range' (a+c+b) a=List.range' 0 (a+c+b+a) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=a+c+b) (n:=a))
    rw [hdc,hdcb,hdcba]
    simp only [Nat.zero_add,←List.range_eq_range']
    congr 1; omega
  simpa only [full,C,cap,chainLength,chainStart,chamberLabels_full,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three,
    Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ',Matrix.vecHead,Matrix.vecTail,
    List.append_assoc] using hall

private theorem bank_inventory (asc : Bool) (a b c v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (hv : v<2^(a-1)) (hw : w<2^((if asc then c else b)-1)) :
    (word asc a b c v w).Perm (List.range (a+b+c+a)) := by
  have hu := complement_inventory (a-1) 0 v hv
  have hu' : (C a b c 0 (cap a-v) ++ C a b c 0 v).Perm (full a b c 0) := by
    simpa [C,full,cap,chainLength,chainStart,chamberLabels_full] using hu
  have split (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a r-1)) :
      (C a b c r (cap (chainLength a b c a r)-m) ++ C a b c r m).Perm
        (full a b c r) := by
    simpa [C,full,cap,chamberLabels_full] using
      complement_inventory (chainLength a b c a r-1) (chainStart b c a r) m hm
  apply Multiset.coe_eq_coe.mp
  rw [←all_chains a b c ha hb hc]
  cases asc
  · have hw' := split 2 w (by simpa [chainLength] using hw)
    have u := Multiset.coe_eq_coe.mpr hu'
    have w' := Multiset.coe_eq_coe.mpr hw'
    simp only [←Multiset.coe_add] at u w'
    calc
      (word false a b c v w : Multiset ℕ) =
          ↑(full a b c 3)+↑(full a b c 1)+
          (↑(C a b c 0 (cap a-v))+↑(C a b c 0 v))+
          (↑(C a b c 2 (cap b-w))+↑(C a b c 2 w))+
          {a+b+c+a-1}+{a+c-1}+{a-1}+{a+c+b-1} := by
        dsimp [word,bank,terminal]
        simp [word,bank,terminal]
        ac_rfl
      _ = _ := by rw [u,w']; simp only [←Multiset.coe_add,Multiset.coe_singleton]; ac_rfl
  · have hw' := split 1 w (by simpa [chainLength] using hw)
    have u := Multiset.coe_eq_coe.mpr hu'
    have w' := Multiset.coe_eq_coe.mpr hw'
    simp only [←Multiset.coe_add] at u w'
    calc
      (word true a b c v w : Multiset ℕ) =
          ↑(full a b c 3)+↑(full a b c 2)+
          (↑(C a b c 0 (cap a-v))+↑(C a b c 0 v))+
          (↑(C a b c 1 (cap c-w))+↑(C a b c 1 w))+
          {a+b+c+a-1}+{a-1}+{a+c-1}+{a+c+b-1} := by
        dsimp [word,bank,terminal]
        simp [word,bank,terminal]
        ac_rfl
      _ = _ := by rw [u,w']; simp only [←Multiset.coe_add,Multiset.coe_singleton]; ac_rfl

private theorem bank_good (asc : Bool) (a b c v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (j : Fin 4) (i : ℕ)
    (hi : i∈bank asc a b c v w j) : i<size a b c a ∧ i∉negatives a b c a := by
  have masked (r : Fin 4) (m : ℕ) (hm : i∈C a b c r m) :
      chainStart b c a r ≤ i ∧ i < chainStart b c a r + chainLength a b c a r - 1 := by
    obtain ⟨e,he,_,hei⟩ := (chamberLabels_mem _ _ _ _).mp hm
    omega
  cases asc <;> fin_cases j
  all_goals dsimp [bank,full] at hi
  all_goals simp only [List.mem_append] at hi
  all_goals repeat' first
    | rcases hi with hi|hi
    | (have h := masked _ _ hi
       dsimp [chainStart,chainLength] at h
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)

private theorem bank_nodup (asc : Bool) (a b c v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (hv : v<2^(a-1)) (hw : w<2^((if asc then c else b)-1)) (j : Fin 4) :
    (bank asc a b c v w j).Nodup := by
  have h := (bank_inventory asc a b c v w ha hb hc hv hw).nodup_iff.mpr
    List.nodup_range
  dsimp [word] at h
  simp only [List.nodup_append,List.nodup_cons] at h
  fin_cases j <;> aesop

private def masses (asc : Bool) (a b c v w : ℕ) (F : Fin 4 → ℤ) : Fin 4 → ℤ :=
  let cu : ℤ := cap a; let cv : ℤ := cap c; let cw : ℤ := cap b
  if asc then ![cu*F 3,(cu-v)*F 0,(cv-w)*F 1,cw*F 2+v*F 0+w*F 1]
  else ![cu*F 3,cv*F 1+v*F 0+w*F 2,(cu-v)*F 0,(cw-w)*F 2]

private theorem physical_W_one (a b c : ℕ) (hb : 2≤b) : C a b c 2 1=[a+c] := by
  have hlen : 0<b-1 := by omega
  have hperm : (C a b c 2 1).Perm [a+c] := by
    apply (List.perm_ext_iff_of_nodup (chamberLabels_nodup _ _ _) (by simp)).mpr
    intro i
    simp only [C,chainLength,chainStart,Matrix.cons_val_two,chamberLabels_mem,List.mem_singleton]
    constructor
    · rintro ⟨e,he,hbit,hei⟩
      change (2^0:ℕ).testBit e=true at hbit
      have he0 : 0=e := of_decide_eq_true (by simpa only [Nat.testBit_two_pow] using hbit)
      subst e; omega
    · intro hi; exact ⟨0,hlen,by decide,by omega⟩
  have hlen' := hperm.length_eq
  cases he : C a b c 2 1 with
  | nil => simp [he] at hlen'
  | cons x xs =>
    have hxs : xs=[] := by simpa [he] using hlen'
    have hx : x=a+c := by
      have hm := hperm.mem_iff.mp (show x∈C a b c 2 1 by simp [he])
      simpa using hm
    simp [he,hxs,hx]

private theorem bank_masses (asc : Bool) (a b c v w : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c)
    (hv : v<2^(a-1)) (hw : w<2^((if asc then c else b)-1)) (side : Bool) :
    let F := if side then newBase a b c a else base a b c a
    let f := if side then newValue a b c a else oldValue a b c a
    ∀ j : Fin 4, ((bank asc a b c v w j).map f).sum=masses asc a b c v w F j := by
  dsimp only
  let F := if side then newBase a b c a else base a b c a
  let f := if side then newValue a b c a else oldValue a b c a
  have table := chain_values a b c a ha hb hc ha
  have sum (r : Fin 4) (m : ℕ) (hm : m<2^(chainLength a b c a r-1)) :
      ((C a b c r m).map f).sum=(m:ℤ)*F r := by
    by_cases hW : r=2 ∧ m=1
    · rcases hW with ⟨rfl,rfl⟩
      rw [physical_W_one a b c hb]
      simp only [List.map_singleton,List.sum_singleton,Nat.cast_one,one_mul]
      cases side
      · dsimp [F,f]
        simpa [chainStart,chainLength] using
          (table.2.1 2 0 (by simp [chainLength]; omega)).trans (if_pos (by simp [chainLength]; omega))
      · dsimp [F,f]
        simpa [chainStart,chainLength] using
          (table.2.2.1 2 0 (by simp [chainLength]; omega)).trans (if_pos (by simp [chainLength]; omega))
    · apply chamberLabels_sum _ _ m hm f (F r)
      intro e he
      cases side
      · dsimp [F,f]
        exact (table.2.1 r e (by omega)).trans (if_pos (by omega))
      · dsimp [F,f]
        exact (table.2.2.1 r e (by omega)).trans (if_pos (by omega))
  have fullsum (r : Fin 4) : ((full a b c r).map f).sum=
      (cap (chainLength a b c a r):ℤ)*F r :=
    sum r _ (by dsimp [cap]; have := Nat.two_pow_pos (chainLength a b c a r-1); omega)
  have hvc := complement_stock a v hv
  cases side <;> dsimp [F,f] at *
  cases asc <;> intro j <;> fin_cases j
  all_goals dsimp [bank,masses]
  all_goals simp only [List.map_append,List.sum_append]
  all_goals first
    | exact fullsum 3
    | (rw [sum 0 _ (by simpa [chainLength] using hvc.2),Nat.cast_sub hvc.1])
    | (have hwc := complement_stock c w (by simpa using hw)
       rw [sum 1 _ (by simpa [chainLength] using hwc.2),Nat.cast_sub hwc.1])
    | (have hwc := complement_stock b w (by simpa using hw)
       rw [sum 2 _ (by simpa [chainLength] using hwc.2),Nat.cast_sub hwc.1])
    | (rw [fullsum 1,sum 0 v (by simpa [chainLength] using hv),
         sum 2 w (by simpa [chainLength] using hw)])
    | (rw [fullsum 2,sum 0 v (by simpa [chainLength] using hv),
         sum 1 w (by simpa [chainLength] using hw)])


end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
