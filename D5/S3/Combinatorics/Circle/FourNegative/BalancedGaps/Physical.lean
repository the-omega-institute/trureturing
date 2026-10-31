/- GID: D5/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Physical
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/BalancedGaps/Physical
   mirror-E: none(waiver:consumed-labelled-partition)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact physical partitions with three single low-bit transfers. -/
import D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Arithmetic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
open PacketNormalForm
open private offsets order ear transfer correction
  from D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps.Arithmetic
open private size chainStart chainLength negatives
  from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open private blocksWord from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Structure
open private orderedPackets from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Certificate

private def positivePacket (a b c d : ℕ) (r : Fin 4) : Finset ℕ :=
  Finset.Ico (chainStart b c d r) (chainStart b c d r + (chainLength a b c d r-1))
private def negativeLabel (a b c d : ℕ) (r : Fin 4) : ℕ :=
  chainStart b c d r + (chainLength a b c d r-1)
private def assigned (a b c d : ℕ) (n : Fin 16) (r : Fin 4) : Finset ℕ :=
  match transfer n with
  | none => positivePacket a b c d r
  | some (src,dst) =>
    if r=src then (positivePacket a b c d r).erase (chainStart b c d src)
    else if r=dst then insert (chainStart b c d src) (positivePacket a b c d r)
    else positivePacket a b c d r
private def packets (a b c d : ℕ) (n : Fin 16) : List (Finset ℕ × ℕ) :=
  (order n).map (fun r => (assigned a b c d n r,negativeLabel a b c d r))

private theorem native_labels (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (r : Fin 4) :
    (∀ i ∈ positivePacket a b c d r, i < size a b c d ∧ i ∉ negatives a b c d) ∧
    chainStart b c d r ∈ positivePacket a b c d r := by
  fin_cases r <;>
    simp only [positivePacket,chainStart,chainLength,Finset.mem_Ico,negatives,
      List.mem_cons,List.mem_nil_iff,or_false,size] <;> constructor <;> omega

private theorem assigned_labels (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (n : Fin 16) (r : Fin 4) :
    ∀ i ∈ assigned a b c d n r, i < size a b c d ∧ i ∉ negatives a b c d := by
  have h := native_labels a b c d ha hb hc hd
  have hs (src : Fin 4) := (h src).1 _ (h src).2
  fin_cases n <;> simp only [assigned,transfer,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_succ] <;> try exact (h r).1
  all_goals
    split_ifs <;> intro i hi
    · exact (h r).1 i (Finset.mem_of_mem_erase hi)
    · rcases Finset.mem_insert.mp hi with hi | hi
      · subst i; exact hs _
      · exact (h r).1 i hi
    · exact (h r).1 i hi

private theorem packet_labels (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (n : Fin 16) :
    ∀ b ∈ packets a b c d n, ∀ i ∈ b.1, i < size a b c d ∧ i ∉ negatives a b c d := by
  intro b hb'
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hb'
  exact assigned_labels a b c d ha hb hc hd n r

private theorem negative_order (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (n : Fin 16) :
    ((packets a b c d n).map Prod.snd).Perm (negatives a b c d) := by
  have he : ∀ r : Fin 4, negativeLabel a b c d r = (negatives a b c d)[r.val] := by
    intro r; fin_cases r <;> simp [negativeLabel,chainStart,chainLength,negatives,size] <;> omega
  have hp : (order n).Perm [0,1,2,3] := by fin_cases n <;> decide
  have hh := hp.map (negativeLabel a b c d)
  simpa [packets,List.map_map,Function.comp_def,he,negatives] using hh

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1600000 in
private theorem physical_partition (a b c d : ℕ)
    (ha : 2≤a) (hb : 2≤b) (hc : 2≤c) (hd : 2≤d) (n : Fin 16) :
    (blocksWord (orderedPackets (packets a b c d n)) : Multiset ℕ) =
      (List.range (size a b c d) : Multiset ℕ) := by
  apply Multiset.ext
  intro i
  have hcount (P : Finset ℕ) :
      Multiset.count i (P.toList : Multiset ℕ) = if i∈P then 1 else 0 := by
    rw [Finset.coe_toList]
    exact Multiset.count_eq_of_nodup P.nodup
  have hrange : Multiset.count i (List.range (size a b c d) : Multiset ℕ) =
      if i<size a b c d then 1 else 0 := by
    simpa using (Multiset.count_eq_of_nodup (a:=i)
      (show (List.range (size a b c d) : Multiset ℕ).Nodup from List.nodup_range))
  rw [hrange]
  fin_cases n <;>
    simp only [packets,order,List.map_cons,List.map_nil,orderedPackets,blocksWord,
      Multiset.coe_append,Multiset.coe_cons,Multiset.coe_nil,Multiset.count_add,
      Multiset.count_cons,Multiset.count_zero,hcount] <;>
    simp only [assigned,transfer,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,
      Fin.isValue,Fin.reduceFinMk,ite_true,ite_false,Finset.mem_insert,Finset.mem_erase,
      positivePacket,negativeLabel,chainStart,chainLength,Finset.mem_Ico,size] <;>
    split_ifs <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.BalancedGaps
