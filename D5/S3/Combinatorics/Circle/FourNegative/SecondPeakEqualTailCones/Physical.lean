/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakEqualTailCones/Physical
   generality: I
   mirror-B: none(waiver:private-consumed-physical-construction)
   mirror-E: none(waiver:registered-at-owning-endpoint)
   anchors: [mathlib/module/Mathlib.Data.Nat.Bitwise]
   utility: none
   digest: Two-chain XOR allocation, exact paired masses and physical inventory. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Charts
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
open SourceWidth
open D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.Chambers
open private rank start length f g heads newHeads row_bounds positive_row
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Source
open private p H F C E native_bounds submask_low xor_casts
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Native
open private allocation nativeAllocation dot termOrder
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones.Seams

private def bank (a b s : ℕ) : Fin 4 → List ℕ :=
  let U := chamberLabels (s-1) 0
  let V := chamberLabels (s-1) s
  let W := chamberLabels (b-1) (2*s)
  let X := chamberLabels (a-1) (2*s+b)
  ![U (2^(s-1)-1) ++ W (p a b s),
    V (2^(s-1)-1) ++ W (H b s ^^^ p a b s) ++ X (C a b s),
    W (F b ^^^ H b s), X (E a ^^^ C a b s)]
private def terminal (a b s : ℕ) : Fin 4 → ℕ :=
  ![2*s+b-1,s-1,rank a b s-1,2*s-1]
private def pre (a b s : ℕ) : List ℕ :=
  bank a b s 0 ++ [terminal a b s 0] ++ bank a b s 1 ++ [terminal a b s 1]
private def post (a b s : ℕ) : List ℕ :=
  bank a b s 2 ++ [terminal a b s 2] ++ bank a b s 3 ++ [terminal a b s 3]

private theorem terminal_index (a b s : ℕ) (hs : 2≤s) (ha : 2≤a) (hb : 2≤b)
    (r : Fin 4) :
    terminal a b s r=start b s (termOrder r)+(length a b s (termOrder r)-1) := by
  fin_cases r <;> dsimp [terminal,rank,start,length,termOrder] <;> omega

private theorem native_splits (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    (chamberLabels (b-1) (2*s) (H b s ^^^ p a b s) ++
      chamberLabels (b-1) (2*s) (p a b s)).Perm (chamberLabels (b-1) (2*s) (H b s)) ∧
    (chamberLabels (b-1) (2*s) (F b ^^^ H b s) ++
      chamberLabels (b-1) (2*s) (H b s)).Perm (List.range' (2*s) (b-1)) ∧
    (chamberLabels (a-1) (2*s+b) (E a ^^^ C a b s) ++
      chamberLabels (a-1) (2*s+b) (C a b s)).Perm (List.range' (2*s+b) (a-1)) := by
  have h := native_bounds a b s hs ha hb hbs
  refine ⟨chamberLabels_split _ _ _ _ ?_,?_,?_⟩
  · intro e _ he
    have hel := submask_low _ _ _ h.2.2.2.2.1 he
    simp [H,Nat.testBit_two_pow_sub_one,hel]
  · exact (chamberLabels_split _ _ _ _ (by
      intro e he _; simp [F,Nat.testBit_two_pow_sub_one,he])).trans
      (List.Perm.of_eq (chamberLabels_full _ _))
  · exact (chamberLabels_split _ _ _ _ (by
      intro e he _; simp [E,Nat.testBit_two_pow_sub_one,he])).trans
      (List.Perm.of_eq (chamberLabels_full _ _))

private theorem bank_inventory (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) :
    (pre a b s++post a b s).Perm (List.range (rank a b s)) := by
  have split := native_splits a b s hs ha hb hbs
  let W := chamberLabels (b-1) (2*s)
  let X := chamberLabels (a-1) (2*s+b)
  have hw : (W (p a b s) ++ W (H b s ^^^ p a b s) ++ W (F b ^^^ H b s)).Perm
      (List.range' (2*s) (b-1)) := by
    apply Multiset.coe_eq_coe.mp
    calc
      (↑(W (p a b s) ++ W (H b s ^^^ p a b s) ++ W (F b ^^^ H b s)) : Multiset ℕ) =
          ↑(W (F b ^^^ H b s) ++ (W (H b s ^^^ p a b s) ++ W (p a b s))) := by
        simp only [←Multiset.coe_add]; ac_rfl
      _ = ↑(W (F b ^^^ H b s) ++ W (H b s)) := by
        have hsplit := Multiset.coe_eq_coe.mpr split.1
        simp only [←Multiset.coe_add] at hsplit ⊢
        exact congrArg
          (fun t : Multiset ℕ => (↑(W (F b ^^^ H b s)) : Multiset ℕ)+t) hsplit
      _ = _ := Multiset.coe_eq_coe.mpr split.2.1
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
    (↑(pre a b s++post a b s) : Multiset ℕ) =
        ↑(List.range' 0 (s-1)) + ↑(List.range' s (s-1)) +
        ↑(W (p a b s) ++ W (H b s ^^^ p a b s) ++ W (F b ^^^ H b s)) +
        ↑(X (E a ^^^ C a b s) ++ X (C a b s)) +
        {s-1}+{2*s-1}+{2*s+b-1}+{rank a b s-1} := by
      dsimp [pre,post,bank,terminal,W,X]
      rw [chamberLabels_full,chamberLabels_full]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl
    _ = ↑(List.range' 0 (s-1)) + ↑(List.range' s (s-1)) +
        ↑(List.range' (2*s) (b-1)) + ↑(List.range' (2*s+b) (a-1)) +
        {s-1}+{2*s-1}+{2*s+b-1}+{rank a b s-1} := by
      rw [Multiset.coe_eq_coe.mpr hw,Multiset.coe_eq_coe.mpr split.2.2]
    _ = ↑(List.range (rank a b s)) := by
      rw [←hall]
      simp only [←Multiset.coe_add,Multiset.coe_singleton]
      ac_rfl

private theorem bank_positive (a b s : ℕ) (hs : 2≤s) (ha : s+1≤a)
    (hb : a+1≤b) (side : Bool) :
    ∀ r i, i∈bank a b s r → 0≤(if side then g a b s else f a b s) i := by
  let v := if side then g a b s else f a b s
  let B := if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s)
  have positive (r : Fin 4) (m : ℕ) :
      ∀ i∈chamberLabels (length a b s r-1) (start b s r) m, 0≤v i := by
    apply chamberLabels_positive _ _ _ v (B r)
    · have h := row_bounds a b s (by omega) (by omega) hs
      cases side
      · have hh := (h.1 r).1
        change 0≤heads (2^a) (2^b) (2^s) r
        omega
      · have hh := (h.2 r).1
        change 0≤newHeads (2^a) (2^b) (2^s) r
        omega
    · intro e he
      exact positive_row a b s (by omega) (by omega) hs side r e he
  intro r i hi
  fin_cases r <;> dsimp [bank] at hi
  all_goals try simp only [List.mem_append] at hi
  all_goals repeat' first
    | exact positive 0 _ i hi
    | exact positive 1 _ i hi
    | exact positive 2 _ i hi
    | exact positive 3 _ i hi
    | rcases hi with hi|hi

private theorem bank_masses (a b s : ℕ) (hs : 2≤s)
    (ha : s+1≤a) (hb : a+1≤b) (hbs : 2*s≤b) (side : Bool) :
    ∀ r, ((bank a b s r).map (if side then g a b s else f a b s)).sum=
      dot (if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s))
        (nativeAllocation a b s r) := by
  let v := if side then g a b s else f a b s
  let B := if side then newHeads (2^a) (2^b) (2^s) else heads (2^a) (2^b) (2^s)
  have series (r : Fin 4) : ∀ i<length a b s r-1,
      v (start b s r+i)=(2:ℤ)^i*B r := by
    intro i hi
    exact positive_row a b s (by omega) (by omega) hs side r i hi
  have full (r : Fin 4) :
      ((List.range' (start b s r) (length a b s r-1)).map v).sum=
        ((2:ℤ)^(length a b s r-1)-1)*B r := by
    rw [←chamberLabels_full,chamberLabels_sum _ _ _
      (Nat.sub_lt (Nat.two_pow_pos _) (by decide)) _ _ (series r)]
    rw [Nat.cast_sub (Nat.one_le_two_pow)]
    norm_cast
  have bounds := native_bounds a b s hs ha hb hbs
  have complements := xor_casts a b s hs ha hb hbs
  have hpcap : p a b s<2^(b-1) := by
    have hp := bounds.2.2.2.2.1
    have hh := Nat.pow_le_pow_right Nat.zero_lt_two (show b-s≤b-1 by omega)
    omega
  have wp := chamberLabels_sum (b-1) (2*s) (p a b s) hpcap v (B 2)
    (by simpa [start,length] using series 2)
  have xc := chamberLabels_sum (a-1) (2*s+b) (C a b s) bounds.2.2.2.2.2.2 v (B 3)
    (by simpa [start,length] using series 3)
  have whp := chamberLabels_sum (b-1) (2*s) (H b s ^^^ p a b s)
    (by rw [complements.1]; have hh := bounds.2.2.2.2.2.1; omega)
    v (B 2) (by simpa [start,length] using series 2)
  have wfh := chamberLabels_sum (b-1) (2*s) (F b ^^^ H b s)
    (by rw [complements.2.1]; dsimp [F]; have := Nat.two_pow_pos (b-1); omega)
    v (B 2) (by simpa [start,length] using series 2)
  have xec := chamberLabels_sum (a-1) (2*s+b) (E a ^^^ C a b s)
    (by rw [complements.2.2.1]; dsimp [E]; have := Nat.two_pow_pos (a-1); omega)
    v (B 3) (by simpa [start,length] using series 3)
  rw [complements.2.2.2.1] at whp
  rw [complements.2.2.2.2.1] at wfh
  rw [complements.2.2.2.2.2] at xec
  have su : ((chamberLabels (s-1) 0 (2^(s-1)-1)).map v).sum=
      ((2:ℤ)^(s-1)-1)*B 0 := by
    rw [chamberLabels_full]; simpa [start,length] using full 0
  have sv : ((chamberLabels (s-1) s (2^(s-1)-1)).map v).sum=
      ((2:ℤ)^(s-1)-1)*B 1 := by
    rw [chamberLabels_full]; simpa [start,length] using full 1
  intro r
  fin_cases r <;> dsimp [bank,dot,nativeAllocation,allocation] <;>
    (try simp only [List.map_append,List.sum_append])
  · rw [su,wp]; dsimp [B,v]; ring
  · rw [sv,xc,whp]; dsimp [B,v]; ring
  · rw [wfh]; dsimp [B,v]; ring
  · rw [xec]; dsimp [B,v]; ring

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakEqualTailCones
