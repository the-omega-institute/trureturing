import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail.Algebra
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
open SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private MaskPartition MaskPartition.qcap native_partition
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
open private size base newBase chainLength chainStart oldValue newValue chain_values
  negatives source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-- The low-b physical template also includes the high-b template at v=0. -/
private def bank (a b c d v m : ℕ) : Fin 4 → List ℕ :=
  ![List.range' 0 (d-1),
    List.range' (d+c+b) (a-1) ++ chamberLabels (b-1) (d+c) m ++ chamberLabels (c-1) d v,
    chamberLabels (b-1) (d+c) ((2^(b-1)-1) ^^^ m),
    chamberLabels (c-1) d ((2^(c-1)-1) ^^^ v)]
private def terminal (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d-1,a+b+c+d-1,d+c+b-1,d+c-1]
private def word (a b c d v m : ℕ) : List ℕ :=
  let P := bank a b c d v m
  let t := terminal a b c d
  P 0 ++ t 0 :: P 1 ++ t 1 :: P 2 ++ t 2 :: P 3 ++ [t 3]

private theorem bank_good (a b c d v m : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (j : Fin 4) (i : ℕ) (hi : i∈bank a b c d v m j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have masked (len off mask : ℕ) (hm : i∈chamberLabels len off mask) :
      off≤i ∧ i<off+len := by
    obtain ⟨e,he,_,hei⟩ := (chamberLabels_mem _ _ _ _).mp hm
    omega
  fin_cases j
  all_goals dsimp [bank] at hi
  all_goals try simp only [List.mem_append] at hi
  all_goals repeat' first
    | (have hbound := masked _ _ _ hi
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)
    | (rw [List.mem_range'] at hi
       constructor
       · dsimp [size]; omega
       · simp only [negatives,size,List.mem_cons,List.mem_singleton,List.mem_nil_iff,or_false]; omega)
    | rcases hi with hi|hi

/-- Exact occurrence partition, obtained from the existing native label splitter. -/
private theorem bank_inventory (a b c d v m : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) :
    (word a b c d v m).Perm (List.range (a+b+c+d)) := by
  have split (len off mask : ℕ) :
      (chamberLabels len off mask ++ chamberLabels len off ((2^len-1) ^^^ mask)).Perm
        (List.range' off len) := by
    have hh := chamberLabels_split len off (2^len-1) mask
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
    rw [chamberLabels_full] at hh
    exact (List.perm_append_comm).trans hh
  have wp := split (b-1) (d+c) m
  have vp := split (c-1) d v
  have merge (off len : ℕ) (hl : 1≤len) :
      List.range' off (len-1) ++ [off+len-1]=List.range' off len := by
    simpa only [show off+(len-1)=off+len-1 by omega,show len-1+1=len by omega] using
      (List.range'_1_concat (s:=off) (n:=len-1)).symm
  have hall :
      (List.range' 0 (d-1) ++ [d-1]) ++
      (List.range' d (c-1) ++ [d+c-1]) ++
      (List.range' (d+c) (b-1) ++ [d+c+b-1]) ++
      (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1])=List.range (a+b+c+d) := by
    have h0 := merge 0 d (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge d c (by omega),merge (d+c) b (by omega)]
    rw [show a+b+c+d-1=(d+c+b)+a-1 by omega,merge (d+c+b) a (by omega)]
    simp only [←List.append_assoc]
    have hdc : List.range' 0 d ++ List.range' d c=List.range' 0 (d+c) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d) (n:=c))
    have hdcb : List.range' 0 (d+c) ++ List.range' (d+c) b=List.range' 0 (d+c+b) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c) (n:=b))
    have hdcba : List.range' 0 (d+c+b) ++ List.range' (d+c+b) a=List.range' 0 (d+c+b+a) := by
      simpa only [Nat.zero_add] using (List.range'_append_1 (s:=0) (m:=d+c+b) (n:=a))
    rw [hdc,hdcb,hdcba]
    simp only [Nat.zero_add,←List.range_eq_range']
    congr 1
    omega
  apply Multiset.coe_eq_coe.mp
  calc
    (word a b c d v m : Multiset ℕ)=
        ↑(List.range' 0 (d-1)) +
        ↑(chamberLabels (c-1) d v ++ chamberLabels (c-1) d ((2^(c-1)-1) ^^^ v)) +
        ↑(chamberLabels (b-1) (d+c) m ++ chamberLabels (b-1) (d+c) ((2^(b-1)-1) ^^^ m)) +
        ↑(List.range' (d+c+b) (a-1)) + {d-1}+{d+c-1}+{d+c+b-1}+{a+b+c+d-1} := by
      dsimp [word,bank,terminal]
      simp only [←Multiset.coe_add,Multiset.coe_cons,Multiset.coe_nil]
      ac_rfl
    _=↑(List.range' 0 (d-1)) + ↑(List.range' d (c-1)) +
        ↑(List.range' (d+c) (b-1)) + ↑(List.range' (d+c+b) (a-1)) +
        {d-1}+{d+c-1}+{d+c+b-1}+{a+b+c+d-1} := by
      rw [Multiset.coe_eq_coe.mpr vp,Multiset.coe_eq_coe.mpr wp]
    _=(List.range (a+b+c+d) : Multiset ℕ) := by
      rw [←hall]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

/-- All eight sums are computed with chain_values, not postulated masses. -/
private theorem bank_masses (a b c d v m : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d)
    (hv : v≤2^(c-1)-1) (hm : m≤2^(b-1)-1) :
    ∀ side : Bool,
    let H := if side then newBase a b c d else base a b c d
    let f := if side then newValue a b c d else oldValue a b c d
    let C := fun r : Fin 4 => (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))*H r
    let P := bank a b c d v m
    ((P 0).map f).sum=C 0 ∧
    ((P 1).map f).sum=C 3+(m:ℤ)*H 2+(v:ℤ)*H 1 ∧
    ((P 2).map f).sum=C 2-(m:ℤ)*H 2 ∧
    ((P 3).map f).sum=C 1-(v:ℤ)*H 1 := by
  intro side
  dsimp only
  let H := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  let C := fun r : Fin 4 => (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))*H r
  have tab := chain_values a b c d ha hb hc hd
  have series (r : Fin 4) : ∀ i<chainLength a b c d r-1,
      f (chainStart b c d r+i)=2^i*H r := by
    intro i hi
    cases side
    · exact (tab.2.1 r i (by omega)).trans (if_pos (by omega))
    · exact (tab.2.2.1 r i (by omega)).trans (if_pos (by omega))
  have full (r : Fin 4) :
      ((List.range' (chainStart b c d r) (chainLength a b c d r-1)).map f).sum=C r := by
    rw [←chamberLabels_full]
    apply chamberLabels_sum
    · exact Nat.sub_lt (Nat.two_pow_pos _) (by decide)
    · exact series r
  have split_sum (len off mask : ℕ) (hmask : mask≤2^len-1)
      (head : ℤ) (hseries : ∀ i<len, f (off+i)=2^i*head) :
      ((chamberLabels len off mask).map f).sum=(mask:ℤ)*head ∧
      ((chamberLabels len off ((2^len-1) ^^^ mask)).map f).sum=
        (((2^len-1:ℕ):ℤ)-(mask:ℤ))*head := by
    obtain ⟨hs,hpart⟩ := native_partition len 0 mask hmask
    dsimp only [pow_zero,mul_one,one_mul] at hs hpart
    have hcap : mask<2^len := by have := Nat.two_pow_pos len; omega
    have hcomp : ((2^len-1) ^^^ mask)<2^len := by simpa using MaskPartition.qcap hpart
    have castsum := congrArg (fun n : ℕ => (n:ℤ)) hs
    push_cast at castsum
    refine ⟨chamberLabels_sum len off mask hcap f head hseries,?_⟩
    rw [chamberLabels_sum len off _ hcomp f head hseries]
    congr 1
    omega
  have wseries : ∀ i<b-1, f (d+c+i)=2^i*H 2 := by simpa [chainLength,chainStart] using series 2
  have vseries : ∀ i<c-1, f (d+i)=2^i*H 1 := by simpa [chainLength,chainStart] using series 1
  obtain ⟨wm,wc⟩ := split_sum (b-1) (d+c) m hm (H 2) wseries
  obtain ⟨vm,vc⟩ := split_sum (c-1) d v hv (H 1) vseries
  have fu := full 0
  have fx := full 3
  dsimp [chainStart,chainLength] at fu fx
  dsimp [bank]
  simp only [List.map_append,List.sum_append,fu,fx,wm,vm,wc,vc]
  dsimp [C,chainLength]
  constructor
  · rfl
  constructor
  · rfl
  constructor <;> ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakAdjacentTail
