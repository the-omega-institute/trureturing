/- GID: D5/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue
   generality: I
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/BalancedPhaseMissingResidue
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Balanced actual phases have too few short centers to resolve every residue. -/

import D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockResolution
import Mathlib.Data.Int.Fib.Basic
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue

open D5.S3.Arith.FibonacciAtomic.BottomSiblingBlockCriterion
open D5.S3.Arith.FibonacciAtomic.LiteralWindowEnd
open D5.S3.Arith.ZeckendorfFutureKernel (value advance)
open D5.S3.ConceptDynamics.Experiment.PassiveAdaptiveTranscriptUpperBound
open scoped BigOperators

/-- Width of the integer contribution envelope, with the midpoint rounded down. -/
def envelope (L : Nat) : Nat :=
  (Nat.fib (3 * (L / 2) + 2) - 1) +
    (Nat.fib (3 * (L - L / 2) + 1) - 1)

set_option maxHeartbeats 1000000 in
-- This single proof combines signed sums, a modular recurrence and a finite scan.
/-- A strict center deficit on any complete prime-power factor supplies two
positive actual prefixes at one depth and row, indistinguishable by every
short literal suffix, including errors, with different complete futures. -/
theorem result (H p a L : Nat) (hH : 2 ≤ H) (hp : p.Prime)
    (ha : 1 ≤ a) (hfull : H.factorization p = a) (hL : 1 ≤ L)
    (hsmall : envelope L + 1 < p ^ a - p ^ a / p) :
    ∃ j : Nat, ∃ x y : ActualPrefix,
      x.past.length = j ∧ y.past.length = j ∧ nextRow x = nextRow y ∧
      ((nextRow x).1 : ZMod H) = (Int.fib (-3 * (L / 2 : Nat)) : ZMod H) ∧
      ((nextRow x).2 : ZMod H) = (Int.fib (-3 * (L / 2 : Nat) + 1) : ZMod H) ∧
      0 < sourceNumber x ∧ 0 < sourceNumber y ∧
      (∀ w : List Window, w.length ≤ L → rawIndex H x w = rawIndex H y w) ∧
      ¬ CompleteFutureIndex H x y := by
  classical
  have contribution_bound (H L : Nat) (hH : 2 ≤ H) (hL : 1 ≤ L) :
      (centerImage L H ((Int.fib (-3 * (L / 2 : Nat) : Int) : Int) : ZMod H)
        ((Int.fib (-3 * (L / 2 : Nat) + 1 : Int) : Int) : ZMod H)).card ≤
        envelope L + 1 := by
    classical
    letI : NeZero H := ⟨by omega⟩
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : L ≠ 0)
    let lo (k : Int) (n : Nat) : Int :=
      ∑ i ∈ Finset.range n, min (Int.fib (k + i)) 0
    let hi (k : Int) (n : Nat) : Int :=
      ∑ i ∈ Finset.range n, max (Int.fib (k + i)) 0
    obtain ⟨e, _, _, _, hoff⟩ := (LiteralWindowEnd.result (t + 1)).1
    have signed (k : Int) (w : SuccessfulWord (t + 1)) :
        value (Int.fib k : ZMod H) (Int.fib (k + 1) : ZMod H) (flatten w.val) =
          ((∑ i : Fin (3 * (t + 1) - 1),
            if (e w).val i then Int.fib (k + i.val + 1) else 0 : Int) : ZMod H) := by
      let u : ZMod H := Int.fib k
      let v : ZMod H := Int.fib (k + 1)
      have h := hoff H u.val v.val w
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h
      change value u v (flatten w.val) = _
      rw [h]
      simp only [independentOffset, Nat.cast_sum, Nat.cast_ite, Nat.cast_add,
        Nat.cast_mul, Nat.cast_zero, ZMod.natCast_zmod_val]
      rw [Int.cast_sum]
      apply Finset.sum_congr rfl
      intro i _
      split
      · have hf := Int.fib_add ((i.val : Int) + 1) k
        simp only [add_sub_cancel_right] at hf
        rw [show k + (i.val : Int) + 1 = (i.val : Int) + 1 + k by omega, hf]
        simp only [show (i.val : Int) + 1 = ((i.val + 1 : Nat) : Int) by omega,
          Int.fib_natCast, Int.cast_add, Int.cast_mul, Int.cast_natCast]
        rfl
      · simp only [Int.cast_zero]
    have abs_negative (i : Nat) : |Int.fib (-(i : Int))| = (Nat.fib i : Int) := by
      rw [Int.fib_neg_natCast, abs_mul, abs_neg_one_pow, one_mul,
        abs_of_nonneg (Nat.cast_nonneg _)]
    have positive_sum (n : Nat) :
        ∑ i ∈ Finset.range n, (Nat.fib i : Int) = (Nat.fib (n + 1) : Int) - 1 := by
      have hn := congrArg (fun x : Nat => (x : Int)) (Nat.fib_succ_eq_succ_sum n)
      push_cast at hn
      omega
    have negative_sum (m : Nat) :
        ∑ i ∈ Finset.range m, |Int.fib (-(m : Int) + i)| =
          (Nat.fib (m + 2) : Int) - 1 := by
      rw [← Finset.sum_range_reflect]
      have heq :
          ∑ i ∈ Finset.range m, |Int.fib (-(m : Int) + (m - 1 - i : Nat))| =
            ∑ i ∈ Finset.range m, (Nat.fib (i + 1) : Int) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' := Finset.mem_range.mp hi
        rw [show -(m : Int) + (m - 1 - i : Nat) = -((i + 1 : Nat) : Int) by omega,
          abs_negative]
      rw [heq]
      have hn := positive_sum (m + 1)
      rw [Finset.sum_range_succ'] at hn
      simpa only [Nat.fib_zero, Nat.cast_zero, add_zero] using hn
    let m := 3 * ((t + 1) / 2)
    let n := 3 * ((t + 1) - (t + 1) / 2)
    let k : Int := -(m : Int)
    have hmn : m + n = 3 * (t + 1) := by dsimp [m, n]; omega
    have hsum : hi k (3 * (t + 1)) - lo k (3 * (t + 1)) = (envelope (t + 1) : Int) := by
      have hwidth : hi k (3 * (t + 1)) - lo k (3 * (t + 1)) =
          ∑ i ∈ Finset.range (3 * (t + 1)), |Int.fib (k + i)| := by
        dsimp only [hi, lo]
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [sub_zero] using max_sub_min_eq_abs' (Int.fib (k + i)) 0
      rw [hwidth, ← hmn, Finset.sum_range_add]
      have hpos : (∑ i ∈ Finset.range n, |Int.fib (k + (m + i : Nat))|) =
          (Nat.fib (n + 1) : Int) - 1 := by
        simp only [k, Int.natCast_add, neg_add_cancel_left, Int.fib_natCast,
          Int.abs_natCast]
        exact positive_sum n
      rw [hpos, negative_sum]
      have hm : 1 ≤ Nat.fib (m + 2) := Nat.fib_pos.mpr (by omega)
      have hn : 1 ≤ Nat.fib (n + 1) := Nat.fib_pos.mpr (by omega)
      change _ = ((Nat.fib (m + 2) - 1 : Nat) : Int) +
        ((Nat.fib (n + 1) - 1 : Nat) : Int)
      rw [Nat.cast_sub hm, Nat.cast_sub hn, Nat.cast_one]
    have included :
        centerImage (t + 1) H ((Int.fib k : Int) : ZMod H) ((Int.fib (k + 1) : Int) : ZMod H) ⊆
          (Finset.Icc (lo k (3 * (t + 1))) (hi k (3 * (t + 1)))).image
            (fun x : Int => -(x : ZMod H)) := by
      intro z hz
      obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hz
      let x : Int := ∑ i : Fin (3 * (t + 1) - 1),
        if (e w).val i then Int.fib (k + i.val + 1) else 0
      have lows : (∑ i : Fin (3 * (t + 1) - 1),
          min (Int.fib (k + i.val + 1)) 0) ≤ x := by
        apply Finset.sum_le_sum
        intro i _
        split
        · exact min_le_left _ _
        · exact min_le_right _ _
      have highs : x ≤ (∑ i : Fin (3 * (t + 1) - 1),
          max (Int.fib (k + i.val + 1)) 0) := by
        apply Finset.sum_le_sum
        intro i _
        split
        · exact le_max_left _ _
        · exact le_max_right _ _
      have lo_shift : lo k (3 * (t + 1)) = min (Int.fib k) 0 +
          ∑ i : Fin (3 * (t + 1) - 1), min (Int.fib (k + i.val + 1)) 0 := by
        dsimp only [lo]
        conv_lhs =>
          rw [show 3 * (t + 1) = (3 * (t + 1) - 1) + 1 by omega,
            Finset.sum_range_succ']
        simp only [Int.natCast_zero, add_zero, Int.natCast_add, Int.natCast_one,
          add_assoc]
        rw [add_comm]
        congr 1
        exact (Fin.sum_univ_eq_sum_range (fun i : Nat =>
          min (Int.fib (k + ((i : Int) + 1))) 0) (3 * (t + 1) - 1)).symm
      have hi_shift : hi k (3 * (t + 1)) = max (Int.fib k) 0 +
          ∑ i : Fin (3 * (t + 1) - 1), max (Int.fib (k + i.val + 1)) 0 := by
        dsimp only [hi]
        conv_lhs =>
          rw [show 3 * (t + 1) = (3 * (t + 1) - 1) + 1 by omega,
            Finset.sum_range_succ']
        simp only [Int.natCast_zero, add_zero, Int.natCast_add, Int.natCast_one,
          add_assoc]
        rw [add_comm]
        congr 1
        exact (Fin.sum_univ_eq_sum_range (fun i : Nat =>
          max (Int.fib (k + ((i : Int) + 1))) 0) (3 * (t + 1) - 1)).symm
      have hx : lo k (3 * (t + 1)) ≤ x ∧ x ≤ hi k (3 * (t + 1)) := by
        rw [lo_shift, hi_shift]
        have := min_le_right (Int.fib k) 0
        have := le_max_right (Int.fib k) 0
        omega
      refine Finset.mem_image.mpr ⟨x, Finset.mem_Icc.mpr hx, ?_⟩
      rw [signed]
    have hcard := (Finset.card_le_card included).trans Finset.card_image_le
    rw [Int.card_Icc] at hcard
    have hi : hi k (3 * (t + 1)) + 1 - lo k (3 * (t + 1)) = (envelope (t + 1) + 1 : Nat) := by
      push_cast
      omega
    rw [hi, Int.toNat_natCast] at hcard
    simpa only [k, m, Nat.cast_mul, Nat.cast_ofNat, neg_mul] using hcard

  have row_reachable (H r : Nat) (hH : 2 ≤ H) :
      ∃ source : ActualPrefix,
        ((nextRow source).1 : ZMod H) = (Int.fib (-3 * (r : Int)) : ZMod H) ∧
        ((nextRow source).2 : ZMod H) = (Int.fib (-3 * (r : Int) + 1) : ZMod H) := by
    classical
    letI : NeZero H := ⟨by omega⟩
    let S : Equiv.Perm (ZMod H × ZMod H) := {
      toFun z := (z.2, z.1 + z.2)
      invFun z := (z.2 - z.1, z.1)
      left_inv := by intro z; ext <;> simp
      right_inv := by intro z; ext <;> simp }
    let P := orderOf S
    have hP : 0 < P := orderOf_pos S
    have periodic (z : ZMod H × ZMod H) : advance P z = z := by
      change (S : (ZMod H × ZMod H) → (ZMod H × ZMod H))^[P] z = z
      rw [← Equiv.Perm.coe_pow, pow_orderOf_eq_one]
      rfl
    have add_advance (n m : Nat) (z : ZMod H × ZMod H) :
        advance (n + m) z = advance m (advance n z) := by
      change ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n + m]) z =
        ((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[m])
          (((fun z : ZMod H × ZMod H => (z.2, z.1 + z.2))^[n]) z)
      simpa only [Nat.add_comm] using
        Function.iterate_add_apply (fun z : ZMod H × ZMod H => (z.2, z.1 + z.2)) m n z
    have period_mul (n : Nat) (z : ZMod H × ZMod H) : advance (n * P) z = z := by
      induction n with
      | zero => simp [advance]
      | succ n ih => rw [Nat.succ_mul, add_advance, ih, periodic]
    have fib_row (n : Nat) (k : Int) :
        advance n ((Int.fib k : ZMod H), (Int.fib (k + 1) : ZMod H)) =
          ((Int.fib (k + n) : ZMod H), (Int.fib (k + n + 1) : ZMod H)) := by
      induction n generalizing k with
      | zero => simp [advance]
      | succ n ih =>
        have hf : (Int.fib (k + 2) : ZMod H) =
            (Int.fib k : ZMod H) + (Int.fib (k + 1) : ZMod H) := by
          rw [Int.fib_add_two, Int.cast_add]
        change advance n ((Int.fib (k + 1) : ZMod H),
          (Int.fib k : ZMod H) + (Int.fib (k + 1) : ZMod H)) = _
        rw [← hf, show k + 2 = k + 1 + 1 by omega, ih]
        simp only [Nat.cast_add, Nat.cast_one, add_left_comm, add_comm]
    let j := (r + 2) * P - (r + 1)
    have hj : 1 ≤ j := by
      have := Nat.mul_le_mul_left (r + 2) hP
      dsimp [j]
      omega
    have hidx : 3 * j + 3 * r + 3 = (3 * (r + 2)) * P := by
      have := Nat.mul_le_mul_left (r + 2) hP
      rw [show 3 * (r + 2) * P = 3 * ((r + 2) * P) by ring]
      dsimp [j]
      omega
    have run_append (q : Option (Bool × Bool)) (a b : List Window) :
        run q (a ++ b) = run (run q a) b := by
      induction a generalizing q with
      | nil => rfl
      | cons c cs ih => exact ih (step q c)
    have run_zeros (n : Nat) :
        run (some (false, false)) (List.replicate n .zero) = some (false, false) := by
      induction n with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ, run, step, first, last, nonzero] using ih
    let source : ActualPrefix := ⟨false, List.replicate (j - 1) .zero ++ [.high], by
      rw [run_append, run_zeros]
      rfl⟩
    have hlen : source.past.length = j := by
      change (List.replicate (j - 1) Window.zero ++ [Window.high]).length = j
      simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil]
      omega
    have flat_length (w : List Window) : (flatten w).length = 3 * w.length := by
      induction w with
      | nil => rfl
      | cons b w ih =>
        simp only [flatten, List.flatMap_cons, List.length_append, List.length_cons] at *
        cases b <;> simp only [bits, List.length_cons, List.length_nil] at * <;> omega
    have cast_advance (n : Nat) (a b : Nat) :
        (((advance n (a,b)).1 : ZMod H), ((advance n (a,b)).2 : ZMod H)) =
          advance n ((a : ZMod H), (b : ZMod H)) := by
      induction n generalizing a b with
      | zero => rfl
      | succ n ih =>
        change (((advance n (b, a + b)).1 : ZMod H),
          ((advance n (b, a + b)).2 : ZMod H)) = advance n ((b : ZMod H), _)
        simpa only [Nat.cast_add] using ih b (a + b)
    have hrow : (((nextRow source).1 : ZMod H), ((nextRow source).2 : ZMod H)) =
        advance (3 * j) ((2 : ZMod H),3) := by
      simpa only [nextRow, flat_length, hlen, Nat.cast_ofNat] using
        cast_advance (3 * j) 2 3
    have hbase : advance 3 ((0 : ZMod H), 1) = (2,3) := by
      simp [advance, Function.iterate_succ_apply]
      norm_num
    have hfinal : advance (3 * r) (advance (3 * j) ((2 : ZMod H),3)) = (0,1) := by
      rw [← hbase, ← add_advance, ← add_advance]
      rw [show 3 + (3 * j + 3 * r) = (3 * (r + 2)) * P by omega]
      exact period_mul _ _
    have hnegative : advance (3 * r)
        ((Int.fib (-3 * (r : Int)) : ZMod H),
          (Int.fib (-3 * (r : Int) + 1) : ZMod H)) = (0,1) := by
      rw [fib_row]
      norm_num
    have injective : Function.Injective (advance (R := ZMod H) (3 * r)) := by
      change Function.Injective ((S : (ZMod H × ZMod H) → (ZMod H × ZMod H))^[3 * r])
      exact S.injective.iterate _
    have heq := hrow.trans (injective (hfinal.trans hnegative.symm))
    exact ⟨source, congrArg Prod.fst heq, congrArg Prod.snd heq⟩

  letI : NeZero H := ⟨by omega⟩
  letI : NeZero p := ⟨hp.ne_zero⟩
  let u : ZMod H := Int.fib (-3 * (L / 2 : Nat))
  let v : ZMod H := Int.fib (-3 * (L / 2 : Nat) + 1)
  have hrow : ∃ source : ActualPrefix,
      ((nextRow source).1 : ZMod H) = u ∧ ((nextRow source).2 : ZMod H) = v :=
    row_reachable H (L / 2) hH
  obtain ⟨_, positive, future, index_future, criterion, _, _⟩ :=
    BottomSiblingBlockResolution.result H L hH u v hrow
  let available : Finset (SuccessfulWord L) := Finset.univ
  have centers_bound : (centers L H u v available).card ≤ envelope L + 1 :=
    contribution_bound H L hH hL
  have hp_mem : p ∈ H.primeFactors := by
    rw [← Nat.support_factorization, Finsupp.mem_support_iff, hfull]
    omega
  let axis : H.primeFactors := ⟨p, hp_mem⟩
  let e := H.factorization p
  let S := localCenters L H u v available axis
  let π := D5.S3.Factorization.PrimePowers.PrimeBudgetReadoutDichotomy.primePowerProjection
    p (Nat.sub_le e 1)
  have not_blocks : ¬ BottomBlocks L H u v available := by
    intro blocks
    have lower : (p ^ (e - 1)) * (p - 1) ≤ S.card := by
      have sum_card : S.card =
          ∑ b : ZMod (p ^ (e - 1)), (S.filter fun z => π z = b).card := by
        exact Finset.card_eq_sum_card_fiberwise (by intro z hz; simp)
      rw [sum_card]
      calc
        p ^ (e - 1) * (p - 1) = ∑ _b : ZMod (p ^ (e - 1)), (p - 1) := by
          simp only [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (by intro b _; exact blocks axis b)
    have upper : S.card ≤ envelope L + 1 :=
      Finset.card_image_le.trans centers_bound
    have he : e = a := hfull
    have hpower : p ^ a = p ^ (a - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel ha]
    have hdiv : p ^ a / p = p ^ (a - 1) := by
      rw [hpower, Nat.mul_div_cancel _ hp.pos]
    have hthreshold : p ^ a - p ^ a / p = p ^ (a - 1) * (p - 1) := by
      rw [hdiv, hpower, Nat.mul_sub, Nat.mul_one]
    rw [he] at lower
    rw [hthreshold] at hsmall
    omega
  have not_identifiable : ¬ FiniteIdentifiable L H u v available :=
    fun h => not_blocks ((criterion available).mp h)
  let Q := (↑available : Type)
  let read (w : Q) (source : KnownRowFiber H u v) := rawGcd H source.val w.val.val
  let scan : List Q → PassiveProtocol Q (fun _ => Option Nat) :=
    fun l => l.foldr (fun i rest => .query i (fun _ => rest)) .stop
  have scan_reads (l : List Q) (x y : KnownRowFiber H u v)
      (h : runPassiveProtocol read (scan l) x = runPassiveProtocol read (scan l) y) :
      ∀ i ∈ l, read i x = read i y := by
    induction l with
    | nil => simp
    | cons b bs ih =>
      intro i hi
      simp only [scan, List.foldr_cons, runPassiveProtocol] at h
      obtain ⟨head, tail⟩ := List.cons.inj h
      have hb : read b x = read b y :=
        eq_of_heq (by simpa only [Sigma.mk.inj_iff, true_and] using head)
      rcases List.mem_cons.mp hi with rfl | hi
      · exact hb
      · exact ih tail i hi
  have collision : ∃ x y : KnownRowFiber H u v,
      (∀ w : SuccessfulWord L, rawGcd H x.val w.val = rawGcd H y.val w.val) ∧
      (sourceNumber x.val : ZMod H) ≠ (sourceNumber y.val : ZMod H) := by
    by_contra hc
    apply not_identifiable
    refine ⟨scan Finset.univ.toList, ?_⟩
    intro x y htrace
    by_contra hne
    apply hc
    refine ⟨x, y, ?_, hne⟩
    intro w
    exact scan_reads _ x y htrace ⟨w, Finset.mem_univ _⟩ (by simp)
  obtain ⟨x, y, hshort, hne⟩ := collision
  obtain ⟨j, full⟩ := actual_common_depth_fullness H hH u v hrow
  obtain ⟨x', hxlen, hxres⟩ := full (sourceNumber x.val)
  obtain ⟨y', hylen, hyres⟩ := full (sourceNumber y.val)
  have clone_x : CompleteFuture H x'.val x.val := (future x' x).mpr hxres
  have clone_y : CompleteFuture H y'.val y.val := (future y' y).mpr hyres
  have run_append (q : Option (Bool × Bool)) (a b : List Window) :
      run q (a ++ b) = run (run q a) b := by
    induction a generalizing q with
    | nil => rfl
    | cons c cs ih => exact ih (step q c)
  have failed (source : ActualPrefix) (w : List Window) (hs : ¬ Success w) :
      rawGcd H source w = none := by
    unfold rawGcd observe
    rw [run_append, source.terminal]
    exact if_neg hs
  have index_map (source : ActualPrefix) (w : List Window) :
      rawIndex H source w = (rawGcd H source w).map (fun d => H / d) := by
    unfold rawIndex rawGcd observe
    split <;> rfl
  have flat_length (w : List Window) : (flatten w).length = 3 * w.length := by
    induction w with
    | nil => rfl
    | cons b w ih =>
      simp only [flatten, List.flatMap_cons, List.length_append, List.length_cons] at *
      cases b <;> simp only [bits, List.length_cons, List.length_nil] at * <;> omega
  refine ⟨j, x'.val, y'.val, hxlen, hylen, ?_, x'.property.1, x'.property.2,
    positive x'.val, positive y'.val, ?_, ?_⟩
  · simp only [nextRow, flat_length, hxlen, hylen]
  · intro w hw
    rw [index_map, index_map]
    apply congrArg (fun answer : Option Nat => answer.map (fun d => H / d))
    rw [clone_x w, clone_y w]
    by_cases hs : Success w
    · exact hshort ⟨w, hw, hs⟩
    · rw [failed x.val w hs, failed y.val w hs]
  · intro h
    have hres := (future x' y').mp ((index_future x' y').mp h)
    rw [hxres, hyres] at hres
    exact hne hres

#print axioms result

end D5.S3.Arith.FibonacciAtomic.BalancedPhaseMissingResidue
