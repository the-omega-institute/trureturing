/- GID: D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups
   generality: G
   mirror-B: D5/B/S3/Combinatorics/RotationAvoidance/RotationAvoidanceGroups
   mirror-E: none(waiver:canonical-circular-counting-bijection)
   anchors: [mathlib/module/Mathlib.Tactic]
   utility: none
   digest: Root deletion and increasing relabeling enumerate the eight circular representatives. -/

import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceEnumeration
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceLinear
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceFibonacci
import D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceSymmetry
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGroups

open D5.S3.Combinatorics Nonnesting.NonnestingDefs
open RotationAvoidanceDefs RotationAvoidanceCircular RotationAvoidanceCounts

theorem circular_representative_counts (size : ℕ) (hsize : 1 ≤ size) :
    (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard =
        2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 ∧
    (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard =
        (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
    (circularAvoiders (size + 1) [2, 1, 4, 3]).ncard =
        (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
    (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard = 2 ^ size - size ∧
    (circularAvoiders (size + 1) [1, 2, 4, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard ∧
    (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard = Nat.fib (2 * size - 1) ∧
    (circularAvoiders (size + 1) [1, 4, 2, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard ∧
    (circularAvoiders (size + 1) [2, 4, 1, 3]).ncard =
        (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard ∧
    (5 ≤ size →
      (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard <
          (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
      (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard <
          (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard) := by
  classical
  have rooted_count (q : List ℕ) (patterns : List (List ℕ))
      (hletters : ∀ pattern ∈ patterns, letters pattern = pattern.length)
      (hreduction : ∀ tail, (1 :: tail).Perm (List.range' 1 (size + 1)) →
        ((1 :: tail) ∈ circularAvoiders (size + 1) q ↔
          ∀ pattern ∈ patterns, ¬ Occurs pattern tail)) :
      (circularAvoiders (size + 1) q).ncard =
        (Fishburn.FishburnClassicalDefs.classicalAvoiders size patterns).ncard := by
    let emit := fun word : List ℕ => 1 :: word.map Nat.succ
    have shift (pattern word : List ℕ) (hpattern : pattern ∈ patterns) :
        Occurs pattern (word.map Nat.succ) ↔ Occurs pattern word := by
      unfold Occurs
      rw [hletters pattern hpattern]
      exact ArcherCyclicPadovanPatterns.contains_map_iff pattern word Nat.succ
        (by intro low high hlt; omega)
    have emitPerm (word : List ℕ) (hword : word.Perm (List.range' 1 size)) :
        (emit word).Perm (List.range' 1 (size + 1)) := by
      have hrange : (List.range' 1 size).map Nat.succ = List.range' 2 size := by
        simpa only [show (fun value : ℕ => 1 + value) = Nat.succ by
          funext value; omega, Nat.reduceAdd] using
          List.map_add_range' (a := 1) 1 size 1
      simpa only [emit, hrange, List.range'_succ, Nat.reduceAdd, Nat.mul_one] using
        (hword.map Nat.succ).cons 1
    have emitMember (word : List ℕ)
        (hword : word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders size patterns) :
        emit word ∈ circularAvoiders (size + 1) q := by
      apply (hreduction _ (emitPerm word hword.1)).mpr
      intro pattern hpattern
      exact fun hocc => hword.2 pattern hpattern ((shift pattern word hpattern).mp hocc)
    have emitInjective : Function.Injective emit := by
      intro first second heq
      exact List.map_injective_iff.mpr Nat.succ_injective (List.cons.inj heq).2
    have emitSurjective (circle : List ℕ)
        (hcircle : circle ∈ circularAvoiders (size + 1) q) :
        ∃ word ∈ Fishburn.FishburnClassicalDefs.classicalAvoiders size patterns,
          emit word = circle := by
      obtain ⟨tail, rfl⟩ : ∃ tail, circle = 1 :: tail := by
        cases circle with
        | nil => simp [circularAvoiders] at hcircle
        | cons head tail =>
          have hhead : head = 1 := by simpa using hcircle.2
          exact ⟨tail, by simp [hhead]⟩
      have htailPerm : tail.Perm (List.range' 2 size) := by
        have hp := hcircle.1.1
        rw [List.range'_succ] at hp
        exact List.Perm.cons_inv hp
      let word := tail.map (· - 1)
      have restore : word.map Nat.succ = tail := by
        rw [List.map_map]
        conv_rhs => rw [← List.map_id tail]
        apply List.map_congr_left
        intro value hvalue
        have := List.mem_range'.mp (htailPerm.mem_iff.mp hvalue)
        dsimp
        omega
      have wordPerm : word.Perm (List.range' 1 size) := by
        have hp := htailPerm.map (fun value => value - 1)
        simpa only [word, List.map_sub_range' (by omega : 1 ≤ 2), Nat.reduceSub] using hp
      have tailAvoid := (hreduction tail hcircle.1.1).mp hcircle
      refine ⟨word, ⟨wordPerm, ?_⟩, by simp only [emit, restore]⟩
      intro pattern hpattern hocc
      exact tailAvoid pattern hpattern
        (restore ▸ (shift pattern word hpattern).mpr hocc)
    exact (Set.ncard_congr (fun word _ => emit word) emitMember
      (fun first second _ _ heq => emitInjective heq) (by
        intro circle hcircle
        obtain ⟨word, hword, heq⟩ := emitSurjective circle hcircle
        exact ⟨word, hword, heq⟩)).symm
  have ascending : (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard =
      2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 := by
    rw [rooted_count [1, 2, 3, 4] [[1, 2, 3], [3, 4, 1, 2]] (by
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl) (by
        intro tail hp
        simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] using (minimum_rooted_reductions size tail hp).1)]
    exact RotationAvoidanceEnumeration.ascending_count size
  have binary : (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard = 2 ^ size - size := by
    rw [rooted_count [1, 3, 4, 2] [[2, 3, 1], [2, 1, 3, 4], [4, 2, 1, 3]] (by
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl | rfl <;> rfl) (by
        intro tail hp
        simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] using (minimum_rooted_reductions size tail hp).2.1)]
    exact RotationAvoidanceLinear.binary_separator_count size
  have fibonacci : (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard =
      Nat.fib (2 * size - 1) := by
    rw [rooted_count [1, 3, 2, 4] [[2, 1, 3], [4, 1, 3, 2]] (by
      intro pattern hpattern
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
      rcases hpattern with rfl | rfl <;> rfl) (by
        intro tail hp
        simpa only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq] using (minimum_rooted_reductions size tail hp).2.2)]
    exact RotationAvoidanceFibonacci.fibonacci_count size hsize
  have cancel_counts (q s : List ℕ)
      (heq : (rotationAvoiders (size + 1) (size + 1) q).ncard =
        (rotationAvoiders (size + 1) (size + 1) s).ncard) :
      (circularAvoiders (size + 1) q).ncard =
        (circularAvoiders (size + 1) s).ncard := by
    rw [(counting_cuts (size + 1) (by omega) q).1,
      (counting_cuts (size + 1) (by omega) s).1] at heq
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < size + 1) heq
  have symmetry (q s : List ℕ) (hq : q.Perm [1, 2, 3, 4]) (hs : s ∈ orbit q) :
      (circularAvoiders (size + 1) s).ncard =
        (circularAvoiders (size + 1) q).ncard := by
    exact (cancel_counts q s (RotationAvoidanceSymmetry.orbit_wilfEquivalent
      (size + 1) (by omega) q s hq hs (size + 1) (by omega))).symm
  have cycle (q : List ℕ) (hq : q.Perm [1, 2, 3, 4]) (shift : ℕ)
      (hshift : shift < 4) :
      (circularAvoiders (size + 1) (q.rotate shift)).ncard =
        (circularAvoiders (size + 1) q).ncard := by
    have qlength : q.length = 4 := by simpa using hq.length_eq
    have forward (pattern : List ℕ) (hlen : pattern.length = 4) (offset : ℕ)
        (word : List ℕ) (havoid : ∀ cut < 4, ¬ Occurs (pattern.rotate cut) word) :
        ∀ cut < 4, ¬ Occurs ((pattern.rotate offset).rotate cut) word := by
      intro cut hcut
      rw [List.rotate_rotate, ← List.rotate_mod, hlen]
      exact havoid _ (Nat.mod_lt _ (by omega))
    have restore : (q.rotate shift).rotate (4 - shift) = q := by
      rw [List.rotate_rotate, show shift + (4 - shift) = 4 by omega,
        ← qlength, List.rotate_length]
    have setEq : circularAvoiders (size + 1) (q.rotate shift) =
        circularAvoiders (size + 1) q := by
      ext word
      constructor <;> intro hword
      · have havoid := (all_cuts_iff_cycle_avoidance (size + 1) (by omega)
          (q.rotate shift) word ((List.rotate_perm q shift).trans hq) hword.1.1).mp hword.1
        refine ⟨(all_cuts_iff_cycle_avoidance (size + 1) (by omega) q word hq
          hword.1.1).mpr ?_, hword.2⟩
        simpa only [restore] using forward (q.rotate shift)
          (by simpa using qlength) (4 - shift) word havoid
      · have havoid := (all_cuts_iff_cycle_avoidance (size + 1) (by omega) q word hq
          hword.1.1).mp hword.1
        exact ⟨(all_cuts_iff_cycle_avoidance (size + 1) (by omega) (q.rotate shift)
          word ((List.rotate_perm q shift).trans hq) hword.1.1).mpr
            (forward q qlength shift word havoid), hword.2⟩
    rw [setEq]
  have ascendingReverse : (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard =
      (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard := by
    calc
      _ = (circularAvoiders (size + 1) [4, 3, 2, 1]).ncard :=
        (by simpa only [show ([1, 4, 3, 2] : List ℕ).rotate 1 = [4, 3, 2, 1] by decide]
          using (cycle [1, 4, 3, 2] (by decide) 1 (by omega)).symm)
      _ = _ := symmetry [1, 2, 3, 4] [4, 3, 2, 1] (by decide) (by simp [orbit, complement])
  have ascendingOther : (circularAvoiders (size + 1) [2, 1, 4, 3]).ncard =
      (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard := by
    calc
      _ = (circularAvoiders (size + 1) [1, 4, 3, 2]).ncard := by
        simpa only [show ([1, 4, 3, 2] : List ℕ).rotate 3 = [2, 1, 4, 3] by decide]
          using cycle [1, 4, 3, 2] (by decide) 3 (by omega)
      _ = _ := ascendingReverse
  have binaryOther : (circularAvoiders (size + 1) [1, 2, 4, 3]).ncard =
      (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard := by
    calc
      _ = (circularAvoiders (size + 1) [2, 4, 3, 1]).ncard :=
        (by simpa only [show ([1, 2, 4, 3] : List ℕ).rotate 1 = [2, 4, 3, 1] by decide]
          using (cycle [1, 2, 4, 3] (by decide) 1 (by omega)).symm)
      _ = _ := symmetry [1, 3, 4, 2] [2, 4, 3, 1] (by decide) (by simp [orbit, complement])
  have fibonacciOther : (circularAvoiders (size + 1) [1, 4, 2, 3]).ncard =
      (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
    calc
      _ = (circularAvoiders (size + 1) [3, 2, 4, 1]).ncard :=
        symmetry [3, 2, 4, 1] [1, 4, 2, 3] (by decide) (by simp [orbit, complement])
      _ = _ := by simpa only
        [show ([1, 3, 2, 4] : List ℕ).rotate 1 = [3, 2, 4, 1] by decide]
          using cycle [1, 3, 2, 4] (by decide) 1 (by omega)
  have fibonacciLast : (circularAvoiders (size + 1) [2, 4, 1, 3]).ncard =
      (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
    simpa only [show ([1, 3, 2, 4] : List ℕ).rotate 2 = [2, 4, 1, 3] by decide]
      using cycle [1, 3, 2, 4] (by decide) 2 (by omega)
  have exponential_bounds (index : ℕ) :
      index + 5 + (index + 5).choose 3 < 2 ^ (index + 4) ∧
      1 + (index + 5).choose 2 < 2 ^ (index + 4) ∧
      index + 5 < 2 ^ (index + 4) := by
    induction index with
    | zero => decide
    | succ index ih =>
      have hthree := Nat.choose_succ_succ' (index + 5) 2
      have htwo := Nat.choose_succ_succ' (index + 5) 1
      simp only [Nat.choose_one_right] at htwo
      have hpower : 2 ^ (index + 1 + 4) = 2 * 2 ^ (index + 4) := by
        rw [show index + 1 + 4 = (index + 4) + 1 by omega, pow_succ, Nat.mul_comm]
      simp only [Nat.add_assoc, Nat.reduceAdd] at hthree htwo hpower ⊢
      rw [hpower]
      omega
  let gap := fun count : ℕ => (Nat.fib (2 * count - 1) : ℤ) + 2 * (count : ℤ) + 1 +
    ((count + 1).choose 3 : ℤ) - (2 : ℤ) ^ (count + 1)
  have odd_fibonacci (count : ℕ) (hcount : 1 ≤ count) :
      Nat.fib (2 * (count + 2) - 1) + Nat.fib (2 * count - 1) =
        3 * Nat.fib (2 * (count + 1) - 1) := by
    have hfirst := Nat.fib_add_two (n := 2 * count - 1)
    rw [show 2 * count - 1 + 2 = 2 * count + 1 by omega,
      show 2 * count - 1 + 1 = 2 * count by omega] at hfirst
    have hmiddle := Nat.fib_add_two (n := 2 * count)
    have hlast := Nat.fib_add_two (n := 2 * count + 1)
    have hone : 2 * (count + 1) - 1 = 2 * count + 1 := by omega
    have htwo : 2 * (count + 2) - 1 = 2 * count + 1 + 2 := by omega
    rw [hone, htwo]
    rw [show 2 * count + 1 + 1 = 2 * count + 2 by omega] at hlast
    omega
  have gap_recurrence (count : ℕ) (hcount : 1 ≤ count) :
      gap (count + 2) + gap count = 3 * gap (count + 1) +
        (2 : ℤ) ^ (count + 1) - ((count + 2 : ℕ) : ℤ) -
        ((count + 2).choose 3 : ℤ) := by
    have hf : (Nat.fib (2 * (count + 2) - 1) : ℤ) +
        (Nat.fib (2 * count - 1) : ℤ) = 3 * (Nat.fib (2 * (count + 1) - 1) : ℤ) := by
      exact_mod_cast odd_fibonacci count hcount
    have hthreeNext := Nat.choose_succ_succ' (count + 2) 2
    have hthree := Nat.choose_succ_succ' (count + 1) 2
    have htwo := Nat.choose_succ_succ' (count + 1) 1
    simp only [Nat.choose_one_right] at htwo
    have hthreeNext' : ((count + 3).choose 3 : ℤ) =
        ((count + 2).choose 2 : ℤ) + ((count + 2).choose 3 : ℤ) := by
      exact_mod_cast hthreeNext
    have hthree' : ((count + 2).choose 3 : ℤ) =
        ((count + 1).choose 2 : ℤ) + ((count + 1).choose 3 : ℤ) := by
      exact_mod_cast hthree
    have htwo' : ((count + 2).choose 2 : ℤ) =
        (count : ℤ) + 1 + ((count + 1).choose 2 : ℤ) := by
      exact_mod_cast htwo
    have hpowerNext : (2 : ℤ) ^ (count + 3) = 4 * (2 : ℤ) ^ (count + 1) := by
      rw [show count + 3 = count + 1 + 1 + 1 by omega, pow_succ, pow_succ]
      ring
    have hpower : (2 : ℤ) ^ (count + 2) = 2 * (2 : ℤ) ^ (count + 1) := by
      rw [show count + 2 = count + 1 + 1 by omega, pow_succ]
      ring
    dsimp only [gap]
    simp only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
    rw [hpowerNext, hpower]
    omega
  have increasing_gap (index : ℕ) : 0 < gap (index + 5) ∧
      gap (index + 4) < gap (index + 5) := by
    induction index with
    | zero => decide
    | succ index ih =>
      have hr := gap_recurrence (index + 4) (by omega)
      have hb := (exponential_bounds (index + 1)).1
      have hb' : ((index + 6 : ℕ) : ℤ) + ((index + 6).choose 3 : ℤ) <
          (2 : ℤ) ^ (index + 5) := by
        exact_mod_cast hb
      have hfour : index + 4 + 2 = index + 6 := by omega
      have hfive : index + 4 + 1 = index + 5 := by omega
      rw [hfour, hfive] at hr
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
  have separated (hlarge : 5 ≤ size) :
      (circularAvoiders (size + 1) [1, 3, 4, 2]).ncard <
          (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard ∧
      (circularAvoiders (size + 1) [1, 2, 3, 4]).ncard <
          (circularAvoiders (size + 1) [1, 3, 2, 4]).ncard := by
    rw [ascending, binary, fibonacci]
    have hpower : 2 ^ (size + 1) = 2 * 2 ^ size := by rw [pow_succ, Nat.mul_comm]
    have hbound : size + 1 + (size + 1).choose 3 < 2 ^ size := by
      have := (exponential_bounds (size - 4)).1
      simpa only [show size - 4 + 5 = size + 1 by omega,
        show size - 4 + 4 = size by omega] using this
    have hpositive := (increasing_gap (size - 5)).1
    rw [show size - 5 + 5 = size by omega] at hpositive
    dsimp only [gap] at hpositive
    have ha : 2 * size + 1 + (size + 1).choose 3 < 2 ^ (size + 1) := by omega
    have hcast : (2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 : ℕ) +
        2 * size + 1 + (size + 1).choose 3 = 2 ^ (size + 1) := by omega
    have hcast' :
        ((2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 : ℕ) : ℤ) +
          2 * (size : ℤ) + 1 + ((size + 1).choose 3 : ℤ) = (2 : ℤ) ^ (size + 1) := by
      exact_mod_cast hcast
    constructor
    · omega
    · have : ((2 ^ (size + 1) - 2 * size - 1 - (size + 1).choose 3 : ℕ) : ℤ) <
          (Nat.fib (2 * size - 1) : ℤ) := by omega
      exact_mod_cast this
  exact ⟨ascending, ascendingReverse, ascendingOther, binary, binaryOther,
    fibonacci, fibonacciOther, fibonacciLast, separated⟩

end D5.S3.Combinatorics.RotationAvoidance.RotationAvoidanceGroups
