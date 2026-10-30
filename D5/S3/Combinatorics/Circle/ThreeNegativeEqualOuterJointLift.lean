/- GID: D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/ThreeNegativeEqualOuterJointLift
   mirror-E: none(waiver:no-escape-mirror-specified)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: One physical gamma-beta-alpha schedule and its marked ear for equal outer gaps. -/
import all D5.S3.Combinatorics.Circle.ThreeBitSource
import D5.S3.Combinatorics.Circle.RunFirstEarTransport

/-! A common zero cut for the actual three-negative sources with equal outer gaps. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators

private theorem ladder_sum (f : ℕ → ℤ) (off len : ℕ) (A : ℤ)
    (hf : ∀ i < len, f (off + i) = (2 : ℤ) ^ i * A) :
    ((List.range' off len).map f).sum = (2 ^ len - 1) * A := by
  rw [List.range'_eq_map_range, List.map_map]
  have hm : (List.range len).map (fun i => f (off + i)) =
      (List.range len).map (fun i => (2 : ℤ) ^ i * A) := by
    apply List.map_congr_left
    intro i hi
    exact hf i (List.mem_range.mp hi)
  change ((List.range len).map (fun i => f (off + i))).sum = _
  rw [hm]
  clear hf hm
  induction len with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton, ih, pow_succ]
    ring

private theorem inventory (a b : ℕ) (ha : 2 ≤ a) (hab : a < b) :
    (List.range' (b - 1) a ++ (a + b + a - 1) ::
      List.range' (a + b) (a - 1) ++ (a + b - 1) ::
      (List.range (a - 1) ++ List.range' a (b - a - 1)) ++ [a - 1]).Perm
      (List.range (a + b + a)) := by
  let U := List.range (a - 1)
  let V := List.range' a (b - a - 1)
  let P := List.range' (b - 1) a
  let Q := List.range' (a + b) (a - 1)
  have hU : U ++ [a - 1] = List.range a := by
    simpa only [U, show a = (a - 1) + 1 by omega] using List.range_succ (a - 1)
  have hV : V ++ P = List.range' a (b - 1) := by
    dsimp [V, P]
    convert List.range'_append_1 (s := a) (m := b - a - 1) (n := a) using 1 <;> congr 1 <;> omega
  have hUV : (U ++ [a - 1]) ++ (V ++ P) = List.range (a + b - 1) := by
    rw [hU, hV, List.range_eq_range']
    simpa only [Nat.zero_add, show a + (b - 1) = a + b - 1 by omega] using
      List.range'_append_1 (s := 0) (m := a) (n := b - 1)
  have hB : List.range (a + b - 1) ++ [a + b - 1] = List.range (a + b) := by
    simpa only [show a + b = (a + b - 1) + 1 by omega] using List.range_succ (a + b - 1)
  have hQ : List.range (a + b) ++ Q = List.range (a + b + a - 1) := by
    dsimp [Q]
    rw [List.range_eq_range']
    simpa only [Nat.zero_add, show a + b + (a - 1) = a + b + a - 1 by omega] using
      List.range'_append_1 (s := 0) (m := a + b) (n := a - 1)
  have hG : List.range (a + b + a - 1) ++ [a + b + a - 1] = List.range (a + b + a) := by
    simpa only [show a + b + a = (a + b + a - 1) + 1 by omega] using List.range_succ (a + b + a - 1)
  have hall : (((U ++ [a - 1]) ++ (V ++ P)) ++ [a + b - 1]) ++ Q ++
      [a + b + a - 1] = List.range (a + b + a) := by
    rw [hUV, hB, hQ, hG]
  rw [← hall]
  apply Multiset.coe_eq_coe.mp
  change ((P ++ (a + b + a - 1) :: Q ++ (a + b - 1) ::
    (U ++ V) ++ [a - 1] : List ℕ) : Multiset ℕ) = _
  simp only [List.coe_append, List.coe_cons, List.coe_singleton]
  ac_rfl

private def label (k : ℕ) (hk : 0 < k) (i : ℕ) : Fin k :=
  ⟨i % k, Nat.mod_lt i hk⟩

private theorem lift_order (k t : ℕ) (hk : 0 < k) (l : List ℕ)
    (hp : l.Perm (List.range k))
    (hs : InStrip (fun i => centered (modulus k) ((2 : ℤ) ^ i * t))
      (modulus k / 2) 0 l) :
    OriginalOrder k t (l.map (label k hk)) := by
  let f := fun i : ℕ => centered (modulus k) ((2 : ℤ) ^ i * t)
  have hbase : (List.range k).map (label k hk) = List.finRange k := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      apply Fin.ext
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange, label]
      exact Nat.mod_eq_of_lt (by simpa using hi)
  have hvalue : ∀ i ∈ l, actualSource k t (label k hk i) = f i := by
    intro i hi
    have hib : i < k := List.mem_range.mp (hp.mem_iff.mp hi)
    simp only [actualSource, label, Nat.mod_eq_of_lt hib, f]
  have hm : (l.map (label k hk)).map (actualSource k t) = l.map f := by
    rw [List.map_map]
    exact List.map_congr_left hvalue
  refine ⟨by rw [← hbase]; exact hp.map _, ?_, ?_⟩
  · have ht := (ZeroSumSubsets.source_cycle hk t).2.1
    rw [← List.sum_finRange] at ht
    have hp' := ((hp.map (label k hk)).map (actualSource k t)).sum_eq
    rw [hbase] at hp'
    exact hp'.trans ht
  · intro n
    have hv : ∀ i ∈ l.take n, actualSource k t (label k hk i) = f i :=
      fun i hi => hvalue i (List.mem_of_mem_take hi)
    have hm' := List.map_congr_left hv
    have hn := inStrip_prefix hs n
    simpa only [← List.map_take, List.map_map, hm', zero_add, Set.mem_Icc] using hn

private theorem marked_word (k cut : ℕ) (hk : 0 < k) (P R : List ℕ)
    (hlen : P.length = cut) (hp : (P ++ R).Perm (List.range k)) :
    earWord k ((P ++ R).map (label k hk)) cut =
      (P ++ k :: R).map (label (k + 1) (by omega)) := by
  have hb : ∀ i ∈ P ++ R, i < k := fun i hi => List.mem_range.mp (hp.mem_iff.mp hi)
  have hcast (L : List ℕ) (hL : ∀ i ∈ L, i < k) :
      (L.map (label k hk)).map Fin.castSucc =
        L.map (label (k + 1) (by omega)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    apply Fin.ext
    simp only [label, Fin.val_castSucc, Nat.mod_eq_of_lt (hL i hi),
      Nat.mod_eq_of_lt (show i < k + 1 from by have := hL i hi; omega)]
  have hP := hcast P (fun i hi => hb i (List.mem_append_left R hi))
  have hR := hcast R (fun i hi => hb i (List.mem_append_right P hi))
  have hl : (P.map (label k hk)).length = cut := by simpa using hlen
  simp only [earWord, List.map_append, ← hl, List.take_left, List.drop_left, hP, hR,
    List.map_cons, List.map_append]
  congr 1
  congr 1
  apply Fin.ext
  simp [label, Nat.mod_eq_of_lt (show k < k + 1 by omega)]

end D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift
