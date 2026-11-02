/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakLargeThirdGap/Source
   generality: I
   mirror-B: none(waiver:private-implementation-owned-by-endpoint)
   mirror-E: none(waiver:private-implementation-owned-by-endpoint)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: All physical bank occurrences and their exact paired native source masses. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
import D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Native

/-! All physical bank occurrences and their exact paired native source masses. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
open SourceWidth PeriodicShortening RunFirstEarTransport
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private MaskPartition MaskPartition.hcap MaskPartition.qcap MaskPartition.lowcap
  partition_labels
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap.NativeMasks
open private size base newBase chainLength chainStart oldValue newValue
  chain_values negatives source_signs
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-- Terminal order W,X,U,V; only genuine positive old labels enter each bank. -/
private def bank (a b c d h m low : ℕ) : Fin 4 → List ℕ :=
  ![List.range' 0 (d-1),
    chamberLabels (b-1) (d+c) h,
    chamberLabels (b-1) (d+c) (m ^^^ h) ++ List.range' (d+c+b) (a-1),
    List.range' d (c-1) ++ chamberLabels (b-1) (d+c) low]
private def terminal (a b c d : ℕ) : Fin 4 → ℕ :=
  ![d+c+b-1,a+b+c+d-1,d-1,d+c-1]
private def word (a b c d h m low : ℕ) : List ℕ :=
  let P := bank a b c d h m low
  let T := terminal a b c d
  P 0 ++ T 0 :: P 1 ++ T 1 :: P 2 ++ T 2 :: P 3 ++ [T 3]

/-- The native bit partition is promoted to a permutation of ALL physical labels. -/
private theorem bank_inventory (a b c d h m low : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (part : MaskPartition (b-1) h (m ^^^ h) low) :
    (word a b c d h m low).Perm (List.range (a+b+c+d)) := by
  let W := chamberLabels (b-1) (d+c)
  have hw : (W h ++ W (m ^^^ h) ++ W low).Perm (List.range' (d+c) (b-1)) := by
    simpa only [List.append_assoc] using partition_labels (b-1) (d+c) h (m ^^^ h) low part
  have merge (o len : ℕ) (hlen : 1 ≤ len) :
      List.range' o (len-1) ++ [o+len-1]=List.range' o len := by
    simpa only [show o+(len-1)=o+len-1 by omega,show len-1+1=len by omega] using
      (List.range'_1_concat (s:=o) (n:=len-1)).symm
  have hall :
      (((List.range' 0 (d-1) ++ [d-1]) ++
      (List.range' d (c-1) ++ [d+c-1])) ++
      (List.range' (d+c) (b-1) ++ [d+c+b-1])) ++
      (List.range' (d+c+b) (a-1) ++ [a+b+c+d-1])=List.range (a+b+c+d) := by
    have h0 := merge 0 d (by omega)
    simp only [Nat.zero_add] at h0
    rw [h0,merge d c (by omega),merge (d+c) b (by omega)]
    have hlast : d+c+b+a-1=a+b+c+d-1 := by omega
    rw [←hlast,merge (d+c+b) a (by omega)]
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
  have hword : word a b c d h m low=
      bank a b c d h m low 0 ++ [terminal a b c d 0] ++
      bank a b c d h m low 1 ++ [terminal a b c d 1] ++
      bank a b c d h m low 2 ++ [terminal a b c d 2] ++
      bank a b c d h m low 3 ++ [terminal a b c d 3] := by
    simp only [word,List.append_assoc,List.singleton_append]
  apply Multiset.coe_eq_coe.mp
  calc
    (word a b c d h m low : Multiset ℕ)=
        ↑(List.range' 0 (d-1)) + ↑(List.range' d (c-1)) +
        ↑(W h ++ W (m ^^^ h) ++ W low) + ↑(List.range' (d+c+b) (a-1)) +
        {d-1}+{d+c-1}+{d+c+b-1}+{a+b+c+d-1} := by
      rw [hword]
      dsimp [bank,terminal,W]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl
    _ = ↑(List.range' 0 (d-1)) + ↑(List.range' d (c-1)) +
        ↑(List.range' (d+c) (b-1)) + ↑(List.range' (d+c+b) (a-1)) +
        {d-1}+{d+c-1}+{d+c+b-1}+{a+b+c+d-1} := by
      rw [Multiset.coe_eq_coe.mpr hw]
    _ = (List.range (a+b+c+d) : Multiset ℕ) := by
      rw [←hall]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem bank_good (a b c d h m low : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (j : Fin 4) (i : ℕ) (hi : i∈bank a b c d h m low j) :
    i<size a b c d ∧ i∉negatives a b c d := by
  have masked (len off mask : ℕ) (hm : i∈chamberLabels len off mask) :
      off ≤ i ∧ i<off+len := by
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

/-- Each of the eight bank sums is proved from the actual chain formulas. -/
private theorem bank_masses (a b c d h m low : ℕ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (part : MaskPartition (b-1) h (m ^^^ h) low) :
    ∀ side : Bool,
    let F := if side then newBase a b c d else base a b c d
    let f := if side then newValue a b c d else oldValue a b c d
    let C := fun r : Fin 4 => (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))*F r
    let P := bank a b c d h m low
    ((P 0).map f).sum=C 0 ∧
    ((P 1).map f).sum=(h:ℤ)*F 2 ∧
    ((P 2).map f).sum=((m ^^^ h:ℕ):ℤ)*F 2+C 3 ∧
    ((P 3).map f).sum=C 1+(low:ℤ)*F 2 := by
  intro side
  dsimp only
  let F := if side then newBase a b c d else base a b c d
  let f := if side then newValue a b c d else oldValue a b c d
  let C := fun r : Fin 4 => (((2^(chainLength a b c d r-1)-1:ℕ):ℤ))*F r
  have tab := chain_values a b c d ha hb hc hd
  have series (r : Fin 4) : ∀ i<chainLength a b c d r-1,
      f (chainStart b c d r+i)=2^i*F r := by
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
  have wseries : ∀ i<b-1, f (d+c+i)=2^i*F 2 := by
    simpa [chainLength,chainStart] using series 2
  have sh := chamberLabels_sum (b-1) (d+c) h (MaskPartition.hcap part) f (F 2) wseries
  have sq := chamberLabels_sum (b-1) (d+c) (m ^^^ h) (MaskPartition.qcap part) f (F 2) wseries
  have sl := chamberLabels_sum (b-1) (d+c) low (MaskPartition.lowcap part) f (F 2) wseries
  have su := full 0
  have sv := full 1
  have sx := full 3
  change ((List.range' 0 (d-1)).map f).sum=C 0 at su
  change ((List.range' d (c-1)).map f).sum=C 1 at sv
  change ((List.range' (d+c+b) (a-1)).map f).sum=C 3 at sx
  change ((List.range' 0 (d-1)).map f).sum=C 0 ∧
    ((chamberLabels (b-1) (d+c) h).map f).sum=(h:ℤ)*F 2 ∧
    (((chamberLabels (b-1) (d+c) (m ^^^ h) ++ List.range' (d+c+b) (a-1))).map f).sum=
      ((m ^^^ h:ℕ):ℤ)*F 2+C 3 ∧
    (((List.range' d (c-1) ++ chamberLabels (b-1) (d+c) low)).map f).sum=C 1+(low:ℤ)*F 2
  simp only [List.map_append,List.sum_append,su,sv,sx,sh,sq,sl,and_self]

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakLargeThirdGap
