/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/LowerPhysical
   generality: I
   mirror-B: none(waiver:private-consumed-ceiling-inventory)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Exact ceiling-mask physical word; complement only in the fourth bank. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerSeams
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Physical
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private rank start length f g heads newHeads row_bounds positive_row
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private F E submask_low
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private lowerC lower_mask_facts
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerCeiling
open private dot
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams
open private lowerAllocation lowerNativeAllocation
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.LowerSeams
open private terminal
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Physical

private def lowerBank (a b s : ℕ) : Fin 4 → List ℕ :=
  ![chamberLabels (s-1) 0 (2^(s-1)-1),
    chamberLabels (a-1) (2*s+b) (E a) ++ chamberLabels (b-1) (2*s) (lowerC a b s),
    chamberLabels (s-1) s (2^(s-1)-1),
    chamberLabels (b-1) (2*s) (F b ^^^ lowerC a b s)]
private def lowerPre (a b s : ℕ) : List ℕ :=
  lowerBank a b s 0 ++ [terminal a b s 0] ++ lowerBank a b s 1 ++ [terminal a b s 1]
private def lowerPost (a b s : ℕ) : List ℕ :=
  lowerBank a b s 2 ++ [terminal a b s 2] ++ lowerBank a b s 3 ++ [terminal a b s 3]

private theorem lower_inventory (a b s : ℕ) (hs : 2≤s)
    (ha : 2≤a) (has : a+1≤s) (hb : 2*s+1≤b) :
    (lowerPre a b s++lowerPost a b s).Perm (List.range (rank a b s)) := by
  have bounds := lower_mask_facts a b s hs ha has hb
  have split : (chamberLabels (b-1) (2*s) (F b ^^^ lowerC a b s) ++
      chamberLabels (b-1) (2*s) (lowerC a b s)).Perm (List.range' (2*s) (b-1)) := by
    exact (chamberLabels_split _ _ _ _ (by
      intro e _ he
      have hel := submask_low _ _ _ bounds.1 he
      simp [F,Nat.testBit_two_pow_sub_one,hel])).trans
      (List.Perm.of_eq (chamberLabels_full _ _))
  have merge (o n : ℕ) (hn : 1≤n) :
      List.range' o (n-1)++[o+n-1]=List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega,show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hall :
      (List.range' 0 (s-1)++[s-1]) ++
      (List.range' s (s-1)++[2*s-1]) ++
      (List.range' (2*s) (b-1)++[2*s+b-1]) ++
      (List.range' (2*s+b) (a-1)++[rank a b s-1])=List.range (rank a b s) := by
    have h0 := merge 0 s (by omega)
    have h1 := merge s s (by omega)
    have h2 := merge (2*s) b (by omega)
    have h3 := merge (2*s+b) a (by omega)
    simp only [Nat.zero_add] at h0
    rw [show s+s-1=2*s-1 by omega] at h1
    rw [show (2*s+b)+a-1=rank a b s-1 by dsimp [rank]; omega] at h3
    rw [h0,h1,h2,h3]
    have hj1 : List.range' 0 s++List.range' s s=List.range' 0 (2*s) := by
      simpa [two_mul] using (List.range'_append_1 (s:=0) (m:=s) (n:=s))
    have hj2 : List.range' 0 (2*s)++List.range' (2*s) b=List.range' 0 (2*s+b) := by
      simpa using (List.range'_append_1 (s:=0) (m:=2*s) (n:=b))
    have hj3 : List.range' 0 (2*s+b)++List.range' (2*s+b) a=List.range' 0 (2*s+b+a) := by
      simpa using (List.range'_append_1 (s:=0) (m:=2*s+b) (n:=a))
    rw [hj1,hj2,hj3]
    simp only [←List.range_eq_range']
    congr 1
    dsimp [rank]
    omega
  apply Multiset.coe_eq_coe.mp
  calc
    (↑(lowerPre a b s++lowerPost a b s) : Multiset ℕ) =
        ↑(List.range' 0 (s-1)) + ↑(List.range' s (s-1)) +
        ↑(chamberLabels (b-1) (2*s) (F b ^^^ lowerC a b s) ++
          chamberLabels (b-1) (2*s) (lowerC a b s)) +
        ↑(List.range' (2*s+b) (a-1)) +
        {s-1}+{2*s-1}+{2*s+b-1}+{rank a b s-1} := by
      dsimp [lowerPre,lowerPost,lowerBank,terminal,E]
      rw [chamberLabels_full,chamberLabels_full,chamberLabels_full]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl
    _ = ↑(List.range' 0 (s-1)) + ↑(List.range' s (s-1)) +
        ↑(List.range' (2*s) (b-1)) + ↑(List.range' (2*s+b) (a-1)) +
        {s-1}+{2*s-1}+{2*s+b-1}+{rank a b s-1} := by
      rw [Multiset.coe_eq_coe.mpr split]
    _ = ↑(List.range (rank a b s)) := by
      rw [←hall]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem lower_bank_positive (a b s : ℕ) (hs : 2≤s)
    (ha : 2≤a) (hb : 2≤b) (side : Bool) :
    ∀ r i, i∈lowerBank a b s r → 0≤(if side then g a b s else f a b s) i := by
  let v := if side then g a b s else f a b s
  let B := if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s)
  have positive (r : Fin 4) (m : ℕ) :
      ∀ i∈chamberLabels (length a b s r-1) (start b s r) m, 0≤v i := by
    apply chamberLabels_positive _ _ _ v (B r)
    · have h := row_bounds a b s ha hb hs
      cases side
      · have hh := (h.1 r).1
        change 0≤heads (2^a) (2^b) (2^s) r
        omega
      · have hh := (h.2 r).1
        change 0≤newHeads (2^a) (2^b) (2^s) r
        omega
    · intro e he
      exact positive_row a b s ha hb hs side r e he
  intro r i hi
  fin_cases r <;> dsimp only [lowerBank] at hi
  · exact positive 0 _ i hi
  · rcases List.mem_append.mp hi with hi|hi
    · exact positive 3 _ i hi
    · exact positive 2 _ i hi
  · exact positive 1 _ i hi
  · exact positive 2 _ i hi

private theorem lower_bank_masses (a b s : ℕ) (hs : 2≤s)
    (ha : 2≤a) (has : a+1≤s) (hb : 2*s+1≤b) (side : Bool) :
    ∀ r, ((lowerBank a b s r).map (if side then g a b s else f a b s)).sum=
      dot (if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s))
        (lowerNativeAllocation a b s r) := by
  let v := if side then g a b s else f a b s
  let B := if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s)
  have series (r : Fin 4) : ∀ i<length a b s r-1,
      v (start b s r+i)=(2:ℤ)^i*B r := by
    intro i hi
    exact positive_row a b s ha (by omega) hs side r i hi
  have full (r : Fin 4) :
      ((List.range' (start b s r) (length a b s r-1)).map v).sum=
        ((2:ℤ)^(length a b s r-1)-1)*B r := by
    rw [←chamberLabels_full,chamberLabels_sum _ _ _
      (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) _ _ (series r)]
    rw [Nat.cast_sub Nat.one_le_two_pow]
    norm_cast
  have facts := lower_mask_facts a b s hs ha has hb
  have wc := chamberLabels_sum (b-1) (2*s) (lowerC a b s) facts.1 v (B 2)
    (by simpa [start,length] using series 2)
  have wf := chamberLabels_sum (b-1) (2*s) (F b ^^^ lowerC a b s) facts.2.1 v (B 2)
    (by simpa [start,length] using series 2)
  rw [facts.2.2.2] at wf
  have su : ((chamberLabels (s-1) 0 (2^(s-1)-1)).map v).sum=
      ((2:ℤ)^(s-1)-1)*B 0 := by
    rw [chamberLabels_full]
    simpa [start,length] using full 0
  have sv : ((chamberLabels (s-1) s (2^(s-1)-1)).map v).sum=
      ((2:ℤ)^(s-1)-1)*B 1 := by
    rw [chamberLabels_full]
    simpa [start,length] using full 1
  have sx : ((chamberLabels (a-1) (2*s+b) (E a)).map v).sum=(E a:ℤ)*B 3 := by
    dsimp [E]
    rw [chamberLabels_full,Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    simpa [start,length] using full 3
  intro r
  fin_cases r <;> dsimp only [lowerBank,dot,lowerNativeAllocation,lowerAllocation] <;>
    (try simp only [List.map_append,List.sum_append])
  · rw [su]
    dsimp [B,v]
    ring
  · rw [sx,wc]
    dsimp [B,v]
    ring
  · rw [sv]
    dsimp [B,v]
    ring
  · rw [wf]
    dsimp [B,v]
    ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
