/- GID: D5/S1/Digit/ZeckendorfRawWindow
   generality: I
   mirror-B: none(waiver:source-arithmetic-bridge)
   mirror-E: none(waiver:no-numeric-experiment-declared)
   anchors: [mathlib/module/Mathlib.Data.Nat.Fib.Zeckendorf]
   utility: none
   digest: Decorated canonical Fibonacci windows determine complete partial MSD residuals. -/

import D5.S1.Digit.GoldenBase4IntervalMachine
import D5.S0.Automata.BinaryZeckendorfLanguage
import D5.S1.Words.Powers.GoldenDesubstitutionZeckendorf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Digit.ZeckendorfRawWindow

open D5.S0.Conventions
open D5.S0.Automata.BinaryZeckendorfLanguage
open D5.S1.Digit.GoldenBase4IntervalMachine
open D5.S1.Words
open D5.S1.Words.Powers
open GoldenDesubstitutionZeckendorf

local instance : IsTrans ℕ (fun a b ↦ b + 2 ≤ a) where
  trans _ _ _ hab hbc := by omega

/-- Occupied Fibonacci indices of an arbitrary padded MSD word. -/
def support : List (Fin 2) → List ℕ
  | [] => []
  | a :: w => if a = 0 then support w else (w.length + 2) :: support w

/-- The actual padded MSD value, using the existing Fibonacci two-register evaluation. -/
def value (w : List (Fin 2)) : ℕ := (fibPair w).1

/-- Parity of the number of occupied canonical indices. -/
def parity (n : ℕ) : Bool := decide ((wdigits n).length % 2 = 1)

/-- The two decorations are canonical parity and occupation of the least digit. -/
def q (n : ℕ) : Bool × Bool := (parity n, decide (2 ∈ wdigits n))

/-- Images in the order A=(0,0), B=(1,0), C=(0,1), D=(1,1). -/
def mu (a : Bool × Bool) : List (Bool × Bool) :=
  if a.2 then [(a.1, false)] else [(a.1, false), (!a.1, true)]

/-- A full raw window includes both endpoints. -/
def window (c n : ℕ) : List (Bool × Bool) :=
  (List.range (c + 1)).map (fun i => q (n + i))

/-- Complete partial residual, including malformed continuations. -/
noncomputable def residual (c : ℕ) (w : List (Fin 2)) (z : List (Fin 2)) : Option Bool := by
  classical
  exact if NoAdjacentOnes (w ++ z) then some (parity (value (w ++ z) + c)) else none

/-- Legal padded words have exactly their occupied canonical Fibonacci coordinates.
Both registers are decoded from the same actual occupied indices. -/
theorem source_word_coordinates (w : List (Fin 2)) (hw : NoAdjacentOnes w) :
    (support w).IsZeckendorfRep ∧
    (∀ k ∈ support w, k < w.length + 2) ∧
    ((support w).map Nat.fib).sum = (fibPair w).1 ∧
    ((support w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2 := by
  have hbound : ∀ v : List (Fin 2), ∀ k ∈ support v, k < v.length + 2 := by
    intro v
    induction v with
    | nil => simp [support]
    | cons d v ihv =>
      intro k hk
      by_cases hd : d = 0
      · simp [support, hd] at hk
        have := ihv k hk
        simp only [List.length_cons]
        omega
      · simp [support, hd] at hk
        rcases hk with rfl | hk
        · simp
        · have := ihv k hk
          simp only [List.length_cons]
          omega
  have aux : ∀ w : List (Fin 2), NoAdjacentOnes w →
      (support w).IsZeckendorfRep ∧
      (∀ k ∈ support w, k < w.length + 2) ∧
      ((support w).map Nat.fib).sum = (fibPair w).1 ∧
      ((support w).map (fun k => Nat.fib (k + 1))).sum = (fibPair w).2 := by
    intro w
    induction w with
    | nil => simp [support, fibPair]
    | cons a w ih =>
      intro hw
      have htail : NoAdjacentOnes w := hw.tail
      obtain ⟨hc, hb, hv, hs⟩ := ih htail
      fin_cases a
      · refine ⟨by simpa [support] using hc, hbound _, ?_, ?_⟩
        · simpa [support, fibPair] using hv
        · simpa [support, fibPair] using hs
      · have small : ∀ k ∈ support w, k + 2 ≤ w.length + 2 := by
          cases w with
          | nil => simp [support]
          | cons b t =>
            have hb0 : b = 0 := by
              have := (List.isChain_cons_cons.mp hw).1
              norm_num at this
              exact this
            subst b
            intro k hk
            simp [support] at hk
            have := hbound t k hk
            simp only [List.length_cons]
            omega
        refine ⟨?_, hbound _, ?_, ?_⟩
        · simp only [support]
          rw [if_neg (by decide)]
          rw [List.IsZeckendorfRep, List.cons_append,
            List.isChain_iff_pairwise, List.pairwise_cons]
          exact ⟨fun k hk => by
            rcases List.mem_append.mp hk with hk | hk
            · exact small k hk
            · simp only [List.mem_singleton] at hk
              subst k
              omega, List.isChain_iff_pairwise.mp hc⟩
        · simpa [support, fibPair] using congrArg (fun n => Nat.fib (w.length + 2) + n) hv
        · simpa [support, fibPair] using congrArg (fun n => Nat.fib (w.length + 3) + n) hs
  exact aux w hw

/-- Substitution of an actual numeric interval is exactly the interval between its
actual Fibonacci append-zero boundaries. -/
theorem source_expansion (n t : ℕ) :
    ((List.range t).map (fun i => q (n + i))).flatMap mu =
      (List.range (goldenSubstStart (n + t) - goldenSubstStart n)).map
        (fun i => q (goldenSubstStart n + i)) := by
  classical
  have minIndex (v : ℕ) (k : ℕ) (hk : k ∈ wdigits v) : 2 ≤ k := by
    have hp := List.isChain_iff_pairwise.mp (wdigits_isCanonical v)
    exact (List.pairwise_append.mp hp).2.2 k hk 0 (by simp)
  have first (v : ℕ) : q (goldenSubstStart v) = (parity v, false) := by
    apply Prod.ext
    · simp [q, parity, golden_subst_start_wdigits]
    · simp only [q, Prod.snd, golden_subst_start_wdigits, decide_eq_false_iff_not]
      intro hm
      obtain ⟨k, hk, he⟩ := List.mem_map.mp hm
      have := minIndex v k hk
      omega
  have second (v : ℕ) (hv : 2 ∉ wdigits v) :
      q (goldenSubstStart v + 1) = (!parity v, true) := by
    have hs : wdigits (goldenSubstStart v + 1) =
        (wdigits (goldenSubstStart v)) ++ [2] := by
      symm
      apply wdigits_unique
      · rw [List.IsZeckendorfRep, List.append_assoc, List.isChain_iff_pairwise,
          List.pairwise_append]
        refine ⟨?_, by norm_num, ?_⟩
        · exact (List.pairwise_append.mp
            (List.isChain_iff_pairwise.mp (wdigits_isCanonical _))).1
        · intro a ha b hb
          rw [golden_subst_start_wdigits] at ha
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
          have hk2 := minIndex v k hk
          have hkne : k ≠ 2 := fun he => hv (he ▸ hk)
          have hb' : b = 2 ∨ b = 0 := by simpa using hb
          rcases hb' with rfl | rfl <;> omega
      · simp [List.map_append, decode_wdigits]
    apply Prod.ext
    · simp only [q, Prod.fst, parity, hs, List.length_append,
        List.length_singleton, golden_subst_start_wdigits, List.length_map]
      by_cases he : (wdigits v).length % 2 = 1
      · have ho : ((wdigits v).length + 1) % 2 ≠ 1 := by omega
        simp [he, ho]
      · have ho : ((wdigits v).length + 1) % 2 = 1 := by omega
        simp [he, ho]
    · simp [q, hs]
  have tile (v : ℕ) : mu (q v) =
      (List.range (goldenSubstStart (v + 1) - goldenSubstStart v)).map
        (fun i => q (goldenSubstStart v + i)) := by
    by_cases hv : 2 ∈ wdigits v
    · have hg : goldenWord v = false := by
        simp [goldenWord_eq_zeckendorf_criterion, hv]
      rw [goldenSubstStart_step_false hg]
      conv_lhs => simp [mu, q, hv]
      rw [show goldenSubstStart v + 1 - goldenSubstStart v = 1 by omega]
      norm_num only [List.range_one, List.map_cons, List.map_nil, Nat.add_zero]
      rw [first]
    · have hg : goldenWord v = true := by
        simp [goldenWord_eq_zeckendorf_criterion, hv]
      rw [goldenSubstStart_step_true hg]
      conv_lhs => simp [mu, q, hv]
      rw [show goldenSubstStart v + 2 - goldenSubstStart v = 2 by omega]
      norm_num only [List.range_succ, List.range_zero, List.nil_append,
        List.map_cons, List.map_nil, List.map_append, List.map_singleton, Nat.add_zero]
      rw [first, second v hv]
      rfl
  induction t with
  | zero => simp
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append,
      List.map_singleton, List.flatMap_singleton, ih, tile]
    have h1 := goldenSubstStart_mono (by omega : n ≤ n + t)
    have h2 := goldenSubstStart_mono (by omega : n + t ≤ n + t + 1)
    have harg : n + (t + 1) = n + t + 1 := by omega
    rw [harg]
    have hd : goldenSubstStart (n + t + 1) - goldenSubstStart n =
        (goldenSubstStart (n + t) - goldenSubstStart n) +
          (goldenSubstStart (n + t + 1) - goldenSubstStart (n + t)) := by omega
    rw [hd, List.range_add, List.map_append, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i hi
    congr 1
    dsimp [Function.comp_def]
    omega

/-- Equal actual decorated windows give equal complete Option-valued residuals
on every continuation, with the original padded MSD values and legality domain. -/
theorem window_residual_congruence (c : ℕ) (w v : List (Fin 2))
    (hw : NoAdjacentOnes w) (hv : NoAdjacentOnes v)
    (he : window c (value w) = window c (value v)) :
    residual c w = residual c v := by
  classical
  have coordinates (u : List (Fin 2)) (hu : NoAdjacentOnes u) :
      support u = wdigits (value u) :=
    wdigits_unique (source_word_coordinates u hu).1 (source_word_coordinates u hu).2.2.1
  have minSupport (u : List (Fin 2)) (hu : NoAdjacentOnes u) (k : ℕ)
      (hk : k ∈ support u) : 2 ≤ k := by
    have hp := List.isChain_iff_pairwise.mp (source_word_coordinates u hu).1
    exact (List.pairwise_append.mp hp).2.2 k hk 0 (by simp)
  have lowBit : ∀ u : List (Fin 2), 2 ∈ support u ↔ u.getLast? = some 1 := by
    intro u
    induction u with
    | nil => simp [support]
    | cons a u ih =>
      cases u with
      | nil => fin_cases a <;> simp [support]
      | cons b t =>
        by_cases ha : a = 0
        · simpa [support, ha] using ih
        · simp only [support, if_neg ha, List.mem_cons, List.length_cons,
            List.getLast?_cons_cons] at ⊢
          simpa [support] using ih
  have advance (u : List (Fin 2)) (hu : NoAdjacentOnes u) (a : Fin 2) :
      value (u ++ [a]) = goldenSubstStart (value u) + a.val := by
    have hshift : goldenSubstStart (value u) = (fibPair u).2 := by
      rw [← decode_wdigits (goldenSubstStart (value u)), golden_subst_start_wdigits,
        ← coordinates u hu, List.map_map]
      exact (source_word_coordinates u hu).2.2.2
    change (fibPair (u ++ [a])).1 = _
    rw [fibPair_append_digit]
    exact congrArg (fun n => n + a.val) hshift.symm
  have extension (u : List (Fin 2)) (hu : NoAdjacentOnes u) (a : Fin 2) :
      NoAdjacentOnes (u ++ [a]) ↔ a = 0 ∨ (q (value u)).2 = false := by
    have hlow : 2 ∈ wdigits (value u) ↔ u.getLast? = some 1 := by
      rw [← coordinates u hu, lowBit]
    have hchain : u.IsChain (fun a b => a = 0 ∨ b = 0) := hu
    cases hlast : u.getLast? with
    | none => simp [NoAdjacentOnes, List.isChain_append, hchain, hlast, q, hlow]
    | some b =>
      fin_cases b <;> fin_cases a <;>
        simp [NoAdjacentOnes, List.isChain_append, hchain, hlast, q, hlow]
  have atIndex (a b : ℕ) (hh : window c a = window c b) (i : ℕ) (hi : i ≤ c) :
      q (a + i) = q (b + i) := by
    have hget := congrArg (fun l : List (Bool × Bool) => l[i]?) hh
    simpa [window, List.getElem?_map, List.getElem?_range, show i < c + 1 by omega] using hget
  have derivative (a b : ℕ) (d : Fin 2) (hh : window c a = window c b)
      (hd : d = 0 ∨ (q a).2 = false) :
      window c (goldenSubstStart a + d.val) =
        window c (goldenSubstStart b + d.val) := by
    have h0 : q a = q b := by simpa using atIndex a b hh 0 (by omega)
    have expanded : (window c a).flatMap mu = (window c b).flatMap mu := by rw [hh]
    rw [window, window, source_expansion, source_expansion] at expanded
    have enough (x : ℕ) (hx : d = 0 ∨ (q x).2 = false) :
        c + 1 + d.val ≤ goldenSubstStart (x + (c + 1)) - goldenSubstStart x := by
      rcases hx with rfl | hx
      · have h := goldenSubstStart_add_le x (c + 1)
        simp only [Fin.val_zero]
        omega
      · have hg : goldenWord x = true := by
          simpa [q, goldenWord_eq_zeckendorf_criterion] using hx
        have hstep := goldenSubstStart_step_true hg
        have h := goldenSubstStart_add_le (x + 1) c
        have hdv := d.isLt
        have harg : x + 1 + c = x + (c + 1) := by omega
        rw [harg] at h
        omega
    have ea := enough a hd
    have eb := enough b (by simpa [← h0] using hd)
    apply List.ext_getElem
    · simp [window]
    · intro i hi hj
      have hic : i < c + 1 := by simpa [window] using hi
      have ha : d.val + i < goldenSubstStart (a + (c + 1)) - goldenSubstStart a := by omega
      have hb : d.val + i < goldenSubstStart (b + (c + 1)) - goldenSubstStart b := by omega
      have hget := congrArg (fun l : List (Bool × Bool) => l[d.val + i]?) expanded
      have heq : q (goldenSubstStart a + (d.val + i)) =
          q (goldenSubstStart b + (d.val + i)) := by
        simpa [List.getElem?_map, List.getElem?_range, ha, hb] using hget
      simpa [window, Nat.add_assoc] using heq
  funext z
  induction z generalizing w v with
  | nil =>
    have ht := congrArg Prod.fst (atIndex (value w) (value v) he c le_rfl)
    simpa [residual, hw, hv, q] using congrArg some ht
  | cons a z ih =>
    have h0 : q (value w) = q (value v) := by
      simpa using atIndex (value w) (value v) he 0 (by omega)
    have hd : NoAdjacentOnes (w ++ [a]) ↔ NoAdjacentOnes (v ++ [a]) := by
      rw [extension w hw, extension v hv, h0]
    have assoc (u : List (Fin 2)) : u ++ (a :: z) = (u ++ [a]) ++ z := by simp
    by_cases hw' : NoAdjacentOnes (w ++ [a])
    · have hv' := hd.mp hw'
      have hwin : window c (value (w ++ [a])) = window c (value (v ++ [a])) := by
        rw [advance w hw a, advance v hv a]
        exact derivative _ _ a he ((extension w hw a).mp hw')
      simpa only [residual, assoc] using ih (w ++ [a]) (v ++ [a]) hw' hv' hwin
    · have hv' : ¬ NoAdjacentOnes (v ++ [a]) := by simpa only [← hd] using hw'
      have hbadw : ¬ NoAdjacentOnes ((w ++ [a]) ++ z) :=
        fun h => hw' h.left_of_append
      have hbadv : ¬ NoAdjacentOnes ((v ++ [a]) ++ z) :=
        fun h => hv' h.left_of_append
      simp only [residual, assoc w, assoc v, if_neg hbadw, if_neg hbadv]

#print axioms source_word_coordinates
#print axioms source_expansion
#print axioms window_residual_congruence

end D5.S1.Digit.ZeckendorfRawWindow
