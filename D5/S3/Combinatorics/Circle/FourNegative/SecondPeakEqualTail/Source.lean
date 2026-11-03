/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTail/Source
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exact physical equal-tail banks partition every unchanged original occurrence. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.BitSupports
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! The W, X, U, V terminal order uses the original physical labels. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private Submask from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.Dilation
open private submask_iff from
  D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail.BitSupports
open private size base newBase chainLength chainStart oldValue newValue
  chain_values negatives from
  D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

private def bank (a b c alpha M v J : ℕ) : Fin 4 → List ℕ :=
  ![chamberLabels (b-1) (c+c) ((2^(b-1)-1) ^^^ M) ++
      chamberLabels (a-1) (c+c+b) alpha,
    chamberLabels (a-1) (c+c+b) ((2^(a-1)-1) ^^^ alpha) ++
      chamberLabels (b-1) (c+c) (M ^^^ J) ++ chamberLabels (c-1) c v,
    List.range' 0 (c-1),
    chamberLabels (c-1) c ((2^(c-1)-1) ^^^ v) ++ chamberLabels (b-1) (c+c) J]
private def terminal (a b c : ℕ) : Fin 4 → ℕ :=
  ![c+c+b-1,a+b+c+c-1,c-1,c+c-1]
private def word (a b c alpha M v J : ℕ) : List ℕ :=
  let P := bank a b c alpha M v J
  let T := terminal a b c
  P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]

private theorem bank_inventory (a b c alpha M v J : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hj : Submask J M) :
    (word a b c alpha M v J).Perm (List.range (a+b+c+c)) := by
  let U := List.range' 0 (c-1)
  let V := chamberLabels (c-1) c
  let W := chamberLabels (b-1) (c+c)
  let X := chamberLabels (a-1) (c+c+b)
  let wf := 2^(b-1)-1
  let vf := 2^(c-1)-1
  let xf := 2^(a-1)-1
  have split (len off m : ℕ) :
      (chamberLabels len off ((2^len-1) ^^^ m) ++ chamberLabels len off m).Perm
        (List.range' off len) := by
    simpa only [chamberLabels_full] using chamberLabels_split len off (2^len-1) m
      (by intro e he _; simp [Nat.testBit_two_pow_sub_one,he])
  have hw : (W (wf ^^^ M) ++ W (M ^^^ J) ++ W J).Perm
      (List.range' (c+c) (b-1)) := by
    have h0 := split (b-1) (c+c) M
    have h1 := chamberLabels_split (b-1) (c+c) M J
      (fun e _ he => (submask_iff J M).mp hj e he)
    simpa only [W,wf,List.append_assoc] using
      (h1.append_left (W (wf ^^^ M))).trans h0
  have hx : (X alpha ++ X (xf ^^^ alpha)).Perm (List.range' (c+c+b) (a-1)) :=
    (List.perm_append_comm ..).trans (split (a-1) (c+c+b) alpha)
  have hv : (V v ++ V (vf ^^^ v)).Perm (List.range' c (c-1)) :=
    (List.perm_append_comm ..).trans (split (c-1) c v)
  have merge (o len : ℕ) (hlen : 1 ≤ len) :
      List.range' o (len-1) ++ [o+len-1]=List.range' o len := by
    simpa only [show o+(len-1)=o+len-1 by omega,show len-1+1=len by omega] using
      (List.range'_1_concat (s:=o) (n:=len-1)).symm
  have hall :
      (((List.range' 0 (c-1) ++ [c-1]) ++
        (List.range' c (c-1) ++ [c+c-1])) ++
        (List.range' (c+c) (b-1) ++ [c+c+b-1])) ++
        (List.range' (c+c+b) (a-1) ++ [a+b+c+c-1])=List.range (a+b+c+c) := by
    have hu := merge 0 c (by omega)
    simp only [Nat.zero_add] at hu
    rw [hu,merge c c (by omega),merge (c+c) b (by omega)]
    rw [show a+b+c+c-1=c+c+b+a-1 by omega,merge (c+c+b) a (by omega)]
    rw [show List.range' 0 c ++ List.range' c c=List.range' 0 (c+c) by
      simpa using List.range'_append_1 (s:=0) (m:=c) (n:=c)]
    rw [show List.range' 0 (c+c) ++ List.range' (c+c) b=List.range' 0 (c+c+b) by
      simpa using List.range'_append_1 (s:=0) (m:=c+c) (n:=b)]
    rw [show List.range' 0 (c+c+b) ++ List.range' (c+c+b) a=List.range' 0 (c+c+b+a) by
      simpa using List.range'_append_1 (s:=0) (m:=c+c+b) (n:=a)]
    simp only [Nat.zero_add,←List.range_eq_range']
    congr 1
    omega
  have hword : word a b c alpha M v J=
      bank a b c alpha M v J 0 ++ [terminal a b c 0] ++
      bank a b c alpha M v J 1 ++ [terminal a b c 1] ++
      bank a b c alpha M v J 2 ++ [terminal a b c 2] ++
      bank a b c alpha M v J 3 ++ [terminal a b c 3] := by
    simp only [word,List.append_assoc,List.singleton_append]
  apply Multiset.coe_eq_coe.mp
  calc
    (word a b c alpha M v J : Multiset ℕ)=
        ↑U + ↑(V v ++ V (vf ^^^ v)) +
        ↑(W (wf ^^^ M) ++ W (M ^^^ J) ++ W J) +
        ↑(X alpha ++ X (xf ^^^ alpha)) +
        {c-1}+{c+c-1}+{c+c+b-1}+{a+b+c+c-1} := by
      rw [hword]
      dsimp [bank,terminal,U,V,W,X,wf,vf,xf]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl
    _ = ↑U + ↑(List.range' c (c-1)) + ↑(List.range' (c+c) (b-1)) +
        ↑(List.range' (c+c+b) (a-1)) +
        {c-1}+{c+c-1}+{c+c+b-1}+{a+b+c+c-1} := by
      rw [Multiset.coe_eq_coe.mpr hv,Multiset.coe_eq_coe.mpr hw,Multiset.coe_eq_coe.mpr hx]
    _ = (List.range (a+b+c+c) : Multiset ℕ) := by
      rw [←hall]
      dsimp [U]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem bank_good (a b c alpha M v J : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (j : Fin 4) (i : ℕ) (hi : i∈bank a b c alpha M v J j) :
    i < size a b c c ∧ i∉negatives a b c c := by
  have masked (len off mask : ℕ) (hm : i∈chamberLabels len off mask) :
      off ≤ i ∧ i < off+len := by
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

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTail
