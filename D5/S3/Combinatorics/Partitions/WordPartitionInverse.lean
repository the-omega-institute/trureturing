/- GID: D5/S3/Combinatorics/Partitions/WordPartitionInverse
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Partitions/WordPartitionInverse
   mirror-E: none(waiver:list-recursion-proof)
   anchors: []
   utility: none
   digest: Guarded prefix rows reconstruct the same word and its finite native joint image. -/

import D5.S3.Combinatorics.Partitions.PaddedWordPartition
import D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery
import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace D5.S3.Combinatorics.Partitions.WordPartitionInverse
open scoped BigOperators
open D5.S3.Combinatorics.Partitions.PaddedWordPartition
open D5.S3.Observer.GoldenChronology.BinaryParikhStepTwoBridge
open D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport

def wordOfRows (u : ℕ) : List ℕ → List Bool
  | [] => List.replicate u true
  | a :: l => wordOfRows a l ++ [false] ++ List.replicate (u-a) true

theorem rows_true_power (u : ℕ) : rows (List.replicate u true) = [] := by
  induction u with
  | zero => rfl
  | succ u ih => simp [List.replicate_succ, rows, ih]

theorem rows_append_true_power (w : List Bool) (n : ℕ) :
    rows (w ++ List.replicate n true) = rows w := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_add, List.replicate_one, ← List.append_assoc,
      rows_append_true, ih]

theorem wordOfRows_spec (l : List ℕ) (hl : l.SortedGE) (u : ℕ)
    (hu : ∀ x ∈ l, x ≤ u) :
    (wordOfRows u l).count true = u ∧
    (wordOfRows u l).count false = l.length ∧ rows (wordOfRows u l) = l := by
  induction l generalizing u with
  | nil => simp [wordOfRows, rows_true_power, List.count_replicate]
  | cons a l ih =>
    obtain ⟨hle, htail⟩ := List.pairwise_cons.mp hl.pairwise
    obtain ⟨ht, hf, hr⟩ := ih htail.sortedGE a hle
    have hau : a ≤ u := hu a (by simp)
    refine ⟨?_, ?_, ?_⟩
    · simp [wordOfRows, List.count_append, ht]
      omega
    · simp [wordOfRows, List.count_append, hf, List.count_replicate]
    · rw [wordOfRows, rows_append_true_power, rows_append_false, ht, hr]

theorem wordOfRows_succ (u : ℕ) (l : List ℕ) (hu : ∀ x ∈ l, x ≤ u) :
    wordOfRows (u+1) l = wordOfRows u l ++ [true] := by
  cases l with
  | nil => simp [wordOfRows, List.replicate_add]
  | cons a l =>
    have hau : a ≤ u := hu a (by simp)
    have hs : u+1-a = (u-a)+1 := by omega
    simp only [wordOfRows, hs, List.replicate_add, List.replicate_one, List.append_assoc]

theorem wordOfRows_inverse (w : List Bool) :
    wordOfRows (w.count true) (rows w) = w := by
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w c ih =>
    cases c
    · simp [rows_append_false, wordOfRows, ih]
    · simp [rows_append_true, wordOfRows_succ _ _ (rows_bound w), ih]

theorem wordOfRows_zero_rows (u m : ℕ) :
    wordOfRows u (List.replicate m 0) =
      List.replicate m false ++ List.replicate u true := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih =>
    simp only [List.replicate_succ, wordOfRows, ih,
      Nat.sub_zero, List.replicate_zero, List.append_nil]
    change (List.replicate m false ++ [false]) ++ List.replicate u true =
      (false :: List.replicate m false) ++ List.replicate u true
    rw [← List.replicate_succ']
    rfl

theorem wordOfRows_padding (u : ℕ) (l : List ℕ) (m : ℕ) :
    wordOfRows u (l ++ List.replicate m 0) =
      List.replicate m false ++ wordOfRows u l := by
  induction l generalizing u with
  | nil => simp [wordOfRows_zero_rows, wordOfRows]
  | cons a l ih => simp [wordOfRows, ih, List.append_assoc]

theorem pair_count_bound (w : List Bool) :
    scatteredTrueFalseCount w ≤ w.count true * w.count false := by
  have h := D5.S3.Observer.GoldenChronology.GoldenMagnusParityRecovery.scattered_pair_reversal_sum w
  omega

theorem outer_reverse_contract (w : List Bool) :
    w.reverse.count true = w.count true ∧ w.reverse.count false = w.count false ∧
    scatteredTrueFalseCount w.reverse =
      w.count true * w.count false - scatteredTrueFalseCount w ∧
    (G w.reverse).e = (G w).e ∧ (G w.reverse).f = (G w).f := by
  have hd := congrArg Five.d (G_reverse w)
  rw [all_word_direct, all_word_direct] at hd
  simp only [List.count_reverse] at hd
  have hn := pair_count_bound w
  have hk : scatteredTrueFalseCount w.reverse =
      w.count true * w.count false - scatteredTrueFalseCount w := by
    have hr : (scatteredTrueFalseCount w.reverse : ℝ) =
        ((w.count true * w.count false - scatteredTrueFalseCount w : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn, Nat.cast_mul]
      linarith
    exact_mod_cast hr
  exact ⟨List.count_reverse, List.count_reverse, hk,
    by simpa only using congrArg Five.e (G_reverse w),
    by simpa only using congrArg Five.f (G_reverse w)⟩

def wd (t : Source) : List Bool :=
  (FreeMagma.toFreeSemigroup t).head :: (FreeMagma.toFreeSemigroup t).tail

theorem wd_nonempty (t : Source) : wd t ≠ [] := by simp [wd]
def leftComb (c : Bool) (tail : List Bool) : Source :=
  tail.foldl (fun t d => t * FreeMagma.of d) (FreeMagma.of c)

theorem leftComb_word (c : Bool) (tail : List Bool) :
    wd (leftComb c tail) = c :: tail := by
  have hh := List.foldl_hom wd
    (g₁ := fun t d => t * FreeMagma.of d)
    (g₂ := fun h d => h ++ [d]) (l := tail) (init := FreeMagma.of c)
    (by intro t d; simp [wd,map_mul])
  rw [List.foldl_append_eq_append] at hh
  have hf : (tail.map (fun d => [d])).flatten = tail := by
    change tail.flatMap (fun d => [d]) = tail
    exact List.flatMap_singleton' tail
  simpa [leftComb,wd,hf] using hh.symm

def wordFiber (u v K : ℤ) : Set (List Bool) :=
  {w | w ≠ [] ∧ (w.count true : ℤ) = u ∧ (w.count false : ℤ) = v ∧
    (scatteredTrueFalseCount w : ℤ) = K}
def jointImage (u v K : ℤ) : Set (ℝ × ℝ) :=
  (fun w => ((G w).e,(G w).f)) '' wordFiber u v K
def capacity (u v K : ℤ) : ℕ := (jointImage u v K).ncard
def nativeImage (u v K : ℤ) : Set (ℝ × ℝ) :=
  (fun t : Source => ((G (wd t)).e,(G (wd t)).f)) ''
    {t | ((wd t).count true : ℤ) = u ∧ ((wd t).count false : ℤ) = v ∧
      (scatteredTrueFalseCount (wd t) : ℤ) = K}
def partitionFiber (u v K : ℤ) : Set (List ℕ) :=
  {l | 0 ≤ u ∧ 0 ≤ v ∧ 0 < u+v ∧ 0 ≤ K ∧ K ≤ u*v ∧ l.SortedGE ∧
    (∀ x ∈ l, x ≤ u.toNat) ∧ (l.length : ℤ) = v ∧ (l.sum : ℤ) = K}
def partitionOutput (u v K : ℤ) (l : List ℕ) : ℝ × ℝ :=
  ((u : ℝ)^2*v-6*u*K+6*squareRows l,
    -(u : ℝ)*v^2+6*v*K-6*oddRows l)

theorem wordFiber_guards (u v K : ℤ) (w : List Bool) (hw : w ∈ wordFiber u v K) :
    0 ≤ u ∧ 0 ≤ v ∧ 0 < u+v ∧ 0 ≤ K ∧ K ≤ u*v := by
  obtain ⟨hne,ht,hf,hk⟩ := hw
  have hl := binary_letter_counts_length w
  have hp := pair_count_bound w
  have hpos : 0 < w.length := List.length_pos_iff.mpr hne
  rw [← ht, ← hf, ← hk]
  exact_mod_cast (show 0 ≤ w.count true ∧ 0 ≤ w.count false ∧
    0 < w.count true+w.count false ∧ 0 ≤ scatteredTrueFalseCount w ∧
    scatteredTrueFalseCount w ≤ w.count true*w.count false from by omega)

theorem fiber_finite (u v K : ℤ) : (wordFiber u v K).Finite := by
  apply (List.finite_length_eq Bool (u+v).toNat).subset
  intro w hw
  obtain ⟨_, ht, hf, _⟩ := hw
  have hlen : (w.length : ℤ) = u+v := by
    rw [← binary_letter_counts_length w, Nat.cast_add, ht, hf]
  have hnat := congrArg Int.toNat hlen
  simpa using hnat

theorem native_image_eq (u v K : ℤ) : nativeImage u v K = jointImage u v K := by
  apply Set.Subset.antisymm
  · rintro y ⟨t, ⟨ht,hf,hk⟩, rfl⟩
    exact ⟨wd t, ⟨wd_nonempty t,ht,hf,hk⟩, rfl⟩
  · rintro y ⟨w, ⟨hne,ht,hf,hk⟩, rfl⟩
    cases w with
    | nil => exact False.elim (hne rfl)
    | cons c tail =>
      refine ⟨leftComb c tail, ?_, ?_⟩
      · simpa [leftComb_word] using And.intro ht (And.intro hf hk)
      · simp only [leftComb_word]

theorem joint_image_reverse (u v K : ℤ) :
    jointImage u v K = jointImage u v (u*v-K) := by
  have hsub : ∀ K : ℤ, jointImage u v K ⊆ jointImage u v (u*v-K) := by
    intro K y hy
    obtain ⟨w, ⟨hne,ht,hf,hk⟩, rfl⟩ := hy
    obtain ⟨hrt,hrf,hrk,hre,hrF⟩ := outer_reverse_contract w
    have hri : (scatteredTrueFalseCount w.reverse : ℤ) = u*v-K := by
      rw [hrk, Nat.cast_sub (pair_count_bound w), Nat.cast_mul, ht, hf, hk]
    refine ⟨w.reverse, ⟨?_, ?_, ?_, hri⟩, ?_⟩
    · intro he
      apply hne
      have hh := congrArg List.reverse he
      simpa using hh
    · rw [hrt,ht]
    · rw [hrf,hf]
    · simp only [hre,hrF]
  exact Set.Subset.antisymm (hsub K) (by simpa using hsub (u*v-K))

theorem finite_joint_partition_image (u v K : ℤ) :
    (jointImage u v K).Finite ∧ nativeImage u v K = jointImage u v K ∧
    jointImage u v K = partitionOutput u v K '' partitionFiber u v K ∧
    jointImage u v K = jointImage u v (u*v-K) ∧
    capacity u v K = (nativeImage u v K).ncard := by
  refine ⟨(fiber_finite u v K).image _, native_image_eq u v K, ?_,
    joint_image_reverse u v K, ?_⟩
  · apply Set.Subset.antisymm
    · rintro y ⟨w, hw, rfl⟩
      obtain ⟨gu,gv,gpos,gK,gprod⟩ := wordFiber_guards u v K w hw
      obtain ⟨hne,ht,hf,hk⟩ := hw
      have hun : u.toNat = w.count true := by rw [← ht]; simp
      refine ⟨rows w, ⟨gu,gv,gpos,gK,gprod,rows_sorted w,?_,?_,?_⟩, ?_⟩
      · rw [hun]; exact rows_bound w
      · rw [rows_length,hf]
      · rw [rows_sum,hk]
      · change partitionOutput u v K (rows w) = ((G w).e,(G w).f)
        rw [all_word_direct w]
        simp only [partitionOutput, same_diagram_rows, same_diagram_columns]
        have htr : (w.count true : ℝ) = (u : ℝ) := by exact_mod_cast ht
        have hfr : (w.count false : ℝ) = (v : ℝ) := by exact_mod_cast hf
        have hkr : (scatteredTrueFalseCount w : ℝ) = (K : ℝ) := by exact_mod_cast hk
        simp [htr,hfr,hkr]
    · rintro y ⟨l, ⟨gu,gv,gpos,gK,gprod,hl,hbound,hlen,harea⟩, rfl⟩
      let w := wordOfRows u.toNat l
      obtain ⟨ht,hf,hr⟩ := wordOfRows_spec l hl u.toNat hbound
      have hrw : rows w = l := hr
      have hti : (w.count true : ℤ) = u := by
        dsimp [w]; rw [ht,Int.toNat_of_nonneg gu]
      have hfi : (w.count false : ℤ) = v := by dsimp [w]; rw [hf,hlen]
      have hki : (scatteredTrueFalseCount w : ℤ) = K := by
        rw [← rows_sum, hr, harea]
      have hne : w ≠ [] := by
        intro he
        have hz : u+v = 0 := by
          rw [← hti, ← hfi, he]; simp
        omega
      refine ⟨w, ⟨hne,hti,hfi,hki⟩, ?_⟩
      change ((G w).e,(G w).f) = partitionOutput u v K l
      rw [all_word_direct w]
      simp only [partitionOutput, same_diagram_rows, same_diagram_columns, hrw]
      have htr : (w.count true : ℝ) = (u : ℝ) := by exact_mod_cast hti
      have hfr : (w.count false : ℝ) = (v : ℝ) := by exact_mod_cast hfi
      have hkr : (scatteredTrueFalseCount w : ℝ) = (K : ℝ) := by exact_mod_cast hki
      simp [htr,hfr,hkr]

  · rw [native_image_eq]
    rfl

end D5.S3.Combinatorics.Partitions.WordPartitionInverse

#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.rows_true_power
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.rows_true_power
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.rows_append_true_power
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.rows_append_true_power
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_spec
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_spec
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_succ
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_succ
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_inverse
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_inverse
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_zero_rows
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_zero_rows
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_padding
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordOfRows_padding
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.pair_count_bound
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.pair_count_bound
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.outer_reverse_contract
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.outer_reverse_contract
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wd
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wd
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wd_nonempty
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wd_nonempty
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.leftComb
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.leftComb
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.leftComb_word
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.leftComb_word
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordFiber
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordFiber
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.jointImage
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.jointImage
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.capacity
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.capacity
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.nativeImage
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.nativeImage
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.partitionFiber
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.partitionFiber
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.partitionOutput
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.partitionOutput
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordFiber_guards
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.wordFiber_guards
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.fiber_finite
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.fiber_finite
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.native_image_eq
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.native_image_eq
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.joint_image_reverse
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.joint_image_reverse
#check D5.S3.Combinatorics.Partitions.WordPartitionInverse.finite_joint_partition_image
#print axioms D5.S3.Combinatorics.Partitions.WordPartitionInverse.finite_joint_partition_image
