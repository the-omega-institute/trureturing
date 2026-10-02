/- GID: D5/S1/Digit/ZeckendorfResidualCover
   generality: I
   mirror-B: none(waiver:source-arithmetic-bridge)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Every complete Fibonacci-shift residual has a bounded legal padded representative. -/

import D5.S1.Digit.ZeckendorfRawWindow
import D5.S1.Digit.GoldenBase4DenseInput
import D5.S1.Digit.GoldenZeckendorfLanguage
import Mathlib.Data.List.Infix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfResidualCover

open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.ZeckendorfRawWindow
open D5.S1.Digit.GoldenBase4AutomataOracle
open D5.S1.Digit.GoldenBase4DenseInput
open D5.S1.Digit.GoldenZeckendorfLanguage
open D5.S1.Words
open D5.S1.Words.Powers

/-- Actual iterated decorated source tiles. -/
def tile : ℕ → Bool × Bool → List (Bool × Bool)
  | 0, a => [a]
  | H + 1, a => (mu a).flatMap (tile H)

/-- Initial numerical segment of the decorated source. -/
def sourcePrefix (n : ℕ) : List (Bool × Bool) :=
  (List.range n).map q

/-- Every legal padded prefix has an equally behaving legal representative of
length H+7. Equality is on the complete Option-valued residual, for all suffixes. -/
theorem all_state_cover (H c : ℕ) (hH : 14 ≤ H) (hc : c ≤ Nat.fib H)
    (w : List (Fin 2))
    (hw : NoAdjacentOnes w) :
    ∃ v : List (Fin 2), NoAdjacentOnes v ∧ v.length = H + 7 ∧
      residual c w = residual c v := by
  classical
  have commute (k : ℕ) (a : Bool × Bool) :
      tile (k + 1) a = (tile k a).flatMap mu := by
    induction k generalizing a with
    | zero => simp [tile]
    | succ k ih =>
      simp only [tile, List.flatMap_assoc]
      apply List.flatMap_congr
      intro b hb
      exact ih b
  have prefix_expand (k n : ℕ) :
      (sourcePrefix n).flatMap (tile k) =
        sourcePrefix ((sourcePrefix n).flatMap (tile k)).length := by
    induction k with
    | zero => simp [tile, sourcePrefix]
    | succ k ih =>
      have e : (sourcePrefix n).flatMap (tile (k + 1)) =
          ((sourcePrefix n).flatMap (tile k)).flatMap mu := by
        rw [List.flatMap_assoc]
        apply List.flatMap_congr
        intro a ha
        exact commute k a
      rw [e, ih]
      let m := ((sourcePrefix n).flatMap (tile k)).length
      have se : (sourcePrefix m).flatMap mu = sourcePrefix (goldenSubstStart m) := by
        simpa only [sourcePrefix, Nat.zero_add, goldenSubstStart_zero, Nat.sub_zero]
          using source_expansion 0 m
      have sl : ((sourcePrefix m).flatMap mu).length = goldenSubstStart m := by
        simpa only [sourcePrefix, List.length_map, List.length_range]
          using congrArg List.length se
      change (sourcePrefix m).flatMap mu = sourcePrefix ((sourcePrefix m).flatMap mu).length
      rw [sl]
      exact se
  have lengths (k : ℕ) (p b : Bool) :
      (tile k (p,b)).length = if b then Nat.fib (k + 1) else Nat.fib (k + 2) := by
    induction k generalizing p b with
    | zero => cases b <;> simp [tile]
    | succ k ih =>
      cases b
      · simp only [tile, mu, Bool.false_eq_true, if_false, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, List.length_append, ih, if_true]
        simpa only [Nat.add_assoc, Nat.add_comm (Nat.fib (k + 2))]
          using (Nat.fib_add_two (n := k + 1)).symm
      · simp [tile, mu, ih, Nat.add_assoc]
  have tile_prefix (k : ℕ) : tile k (false,false) = sourcePrefix (Nat.fib (k + 2)) := by
    have e := prefix_expand k 1
    have hq : q 0 = (false,false) := by simp [q, parity, wdigits]
    simpa [sourcePrefix, hq, lengths] using e
  let R : (Bool × Bool) → (Bool × Bool) → Prop :=
    fun a b => [a,b] <:+: tile 7 (false,false)
  have internal : ∀ a : Bool × Bool, (mu a).IsChain R := by
    decide
  have boundary : ∀ a b : Bool × Bool, R a b →
      ∀ x ∈ (mu a).getLast?, ∀ y ∈ (mu b).head?, R x y := by
    decide
  have mu_nonempty (a : Bool × Bool) : mu a ≠ [] := by
    rcases a with ⟨p,b⟩
    cases b <;> simp [mu]
  have chain_expand (l : List (Bool × Bool)) (hl : l.IsChain R) :
      (l.flatMap mu).IsChain R := by
    rw [List.flatMap_def]
    apply (List.isChain_flatten ?_).mpr
    · refine ⟨?_, ?_⟩
      · intro t ht
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
        exact internal a
      · rw [List.isChain_map]
        exact hl.imp fun a b h => boundary a b h
    · intro hn
      obtain ⟨a, ha, he⟩ := List.mem_map.mp hn
      exact mu_nonempty a he
  have chain_tile (k : ℕ) : (tile k (false,false)).IsChain R := by
    induction k with
    | zero => simp [tile]
    | succ k ih => rw [commute]; exact chain_expand _ ih
  have chain_prefix (n : ℕ) : (sourcePrefix n).IsChain R := by
    have large := Nat.le_fib_add_one (n + 3)
    have hn : n ≤ Nat.fib (n + 3) := by omega
    have e : (sourcePrefix (Nat.fib (n + 3))).take n = sourcePrefix n := by
      simp only [sourcePrefix]
      rw [← List.map_take, List.take_range, Nat.min_eq_left hn]
    rw [← e, ← tile_prefix (n + 1)]
    exact (chain_tile _).take n
  have pairs (n : ℕ) : R (q n) (q (n + 1)) := by
    have hc := chain_prefix (n + 2)
    have hinfix : [q n, q (n + 1)] <:+: sourcePrefix (n + 2) := by
      refine ⟨sourcePrefix n, [], ?_⟩
      simp [sourcePrefix, List.range_succ, List.map_append, List.append_assoc]
    exact List.isChain_pair.mp (hc.infix hinfix)
  let start : ℕ → ℕ := fun j => ((sourcePrefix j).flatMap (tile H)).length
  have start_zero : start 0 = 0 := by simp [start, sourcePrefix]
  have start_step (j : ℕ) : start (j + 1) = start j + (tile H (q j)).length := by
    simp [start, sourcePrefix, List.range_succ]
  have min_length (a : Bool × Bool) : Nat.fib H + 1 ≤ (tile H a).length := by
    have hp := Nat.fib_pos.mpr (show 0 < H - 1 by omega)
    have hf := Nat.fib_add_two (n := H - 1)
    have he : H - 1 + 1 = H := by omega
    have he' : H - 1 + 2 = H + 1 := by omega
    rw [he, he'] at hf
    rcases a with ⟨p,b⟩
    rw [lengths]
    cases b <;> simp only [if_true, Bool.false_eq_true, if_false]
    · have hm := Nat.fib_mono (show H + 1 ≤ H + 2 by omega)
      omega
    · omega
  have start_large (j : ℕ) : j ≤ start j := by
    induction j with
    | zero => omega
    | succ j ih =>
      rw [start_step]
      have := min_length (q j)
      omega
  let n := value w
  have hex : ∃ j, n < start (j + 1) := ⟨n, by have := start_large (n + 1); omega⟩
  let j := Nat.find hex
  have upper : n < start (j + 1) := Nat.find_spec hex
  have lower : start j ≤ n := by
    cases hj : j with
    | zero => simpa [hj, start_zero]
    | succ i =>
      have hi : i < Nat.find hex := by change i < j; omega
      have hh := Nat.find_min hex hi
      change ¬ n < start (i + 1) at hh
      omega
  have source_split : sourcePrefix (start (j + 2)) =
      sourcePrefix (start j) ++ tile H (q j) ++ tile H (q (j + 1)) := by
    rw [← prefix_expand H (j + 2)]
    change (sourcePrefix (j + 2)).flatMap (tile H) = _
    simp only [sourcePrefix, show j + 2 = (j + 1) + 1 by omega,
      List.range_succ, List.map_append, List.map_singleton,
      List.flatMap_append, List.flatMap_singleton]
    change (sourcePrefix j).flatMap (tile H) ++ tile H (q j) ++ tile H (q (j + 1)) = _
    rw [prefix_expand]
    rfl
  obtain ⟨p,t,hpair⟩ := pairs j
  let P := p.flatMap (tile H)
  let U := tile H (q j) ++ tile H (q (j + 1))
  let T := t.flatMap (tile H)
  have target_split : sourcePrefix (Nat.fib (H + 9)) = P ++ U ++ T := by
    have he : tile (H + 7) (false,false) = (tile 7 (false,false)).flatMap (tile H) := by
      have compose (k l : ℕ) (a : Bool × Bool) :
          tile (k + l) a = (tile k a).flatMap (tile l) := by
        induction k generalizing a with
        | zero => simp [tile]
        | succ k ih =>
          rw [show k + 1 + l = (k + l) + 1 by omega, tile, tile, List.flatMap_assoc]
          apply List.flatMap_congr
          intro b hb
          exact ih b
      simpa [Nat.add_comm] using compose 7 H (false,false)
    rw [← tile_prefix (H + 7), he, ← hpair]
    simp [P,U,T,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_assoc]
  let d := n - start j
  have hd : d < (tile H (q j)).length := by
    have := start_step j
    omega
  have fit : d + Nat.fib H + 1 ≤ U.length := by
    have := min_length (q (j + 1))
    simp only [U, List.length_append]
    omega
  have index_in_pair (i : ℕ) (hi : i ≤ Nat.fib H) :
      q (n + i) = q (P.length + d + i) := by
    have hiU : d + i < U.length := by omega
    have hiP : ¬ P.length + (d + i) < P.length := by omega
    have hil : ¬ start j + (d + i) < (sourcePrefix (start j)).length := by
      simp only [sourcePrefix, List.length_map, List.length_range]
      omega
    have hn : n = start j + d := by omega
    have hsrc : n + i < start (j + 2) := by
      have h0 := start_step j
      have h1 := start_step (j + 1)
      rw [show j + 1 + 1 = j + 2 by omega] at h1
      have h2 := min_length (q (j + 1))
      omega
    have htgt : P.length + (d + i) < Nat.fib (H + 9) := by
      have hl := congrArg List.length target_split
      simp only [sourcePrefix, List.length_map, List.length_range, List.length_append] at hl
      omega
    have src : sourcePrefix (start (j + 2)) = sourcePrefix (start j) ++ U := by
      simpa only [U, List.append_assoc] using source_split
    have ea := congrArg (fun l : List (Bool × Bool) => l[start j + (d + i)]?) src
    have eb := congrArg (fun l : List (Bool × Bool) => l[P.length + (d + i)]?) target_split
    have ha : some (q (n + i)) = U[d + i]? := by
      have hidx : start j + (d + i) = n + i := by omega
      simpa [sourcePrefix, List.getElem?_append, hidx, hsrc,
        show ¬ n + i < start j by omega,
        show n + i - start j = d + i by omega] using ea
    have hb : some (q (P.length + d + i)) = U[d + i]? := by
      simp only [List.append_assoc] at eb
      simpa [sourcePrefix, List.getElem?_append, htgt, hiP, hiU,
        Nat.add_assoc] using eb
    exact Option.some.inj (ha.trans hb.symm)
  have hwin : window c n = window c (P.length + d) := by
    apply List.map_congr_left
    intro i hi
    exact index_in_pair i (by have := List.mem_range.mp hi; omega)
  have nbound : P.length + d < Nat.fib (H + 9) := by
    have hl := congrArg List.length target_split
    simp only [sourcePrefix, List.length_map, List.length_range, List.length_append] at hl
    have hU : 0 < U.length := by omega
    omega
  let m := P.length + d
  have len_bound : (zeckendorfMSDWord m).length ≤ H + 7 := by
    rw [length_zeckendorfMSDWord]
    cases hz : wdigits m with
    | nil => simpa [zeckendorfWordLength, hz] using (show 1 ≤ H + 7 by omega)
    | cons a l =>
      have ha : a < H + 9 := by
        have hl : a ≤ Nat.greatestFib m := by
          have hdecode := decode_wdigits m
          rw [hz] at hdecode
          have hf : Nat.fib a ≤ m := by simp only [List.map_cons, List.sum_cons] at hdecode; omega
          exact Nat.le_greatestFib.mpr hf
        have hg : Nat.greatestFib m < H + 9 := Nat.greatestFib_lt.mpr nbound
        omega
      simp only [zeckendorfWordLength, hz]
      omega
  let v := List.replicate (H + 7 - (zeckendorfMSDWord m).length) 0 ++ zeckendorfMSDWord m
  have hv : NoAdjacentOnes v := by
    have hc := zeckendorfMSDWord_noAdjacentOnes m
    have pad (k : ℕ) : NoAdjacentOnes (List.replicate k 0 ++ zeckendorfMSDWord m) := by
      induction k with
      | zero => simpa using hc
      | succ k ih => simpa [List.replicate_succ, NoAdjacentOnes, List.isChain_cons] using ih
    exact pad _
  have vvalue : value v = m := by
    have pad (k : ℕ) : value (List.replicate k 0 ++ zeckendorfMSDWord m) = m := by
      induction k with
      | zero => simpa [value] using zeckendorfMSDWord_value m
      | succ k ih => simpa [List.replicate_succ, value, D5.S1.Digit.GoldenBase4IntervalMachine.fibPair] using ih
    exact pad _
  refine ⟨v,hv,?_,?_⟩
  · simp only [v,List.length_append,List.length_replicate]
    omega
  · apply window_residual_congruence _ _ _ hw hv
    rw [vvalue]
    exact hwin

#print axioms all_state_cover

end D5.S1.Digit.ZeckendorfResidualCover
