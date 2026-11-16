/- GID: D5/S1/Dynamics/Symbolic/KhetanFiniteRecurrence
   generality: G
   mirror-B: none(waiver:no mirrored proof)
   mirror-E: none(waiver:no external mirror)
   anchors: []
   utility: none
   digest: A finite-range bilateral directional recurrence has a uniform global period. -/

import D5.S1.Dynamics.Symbolic.KhetanAnnihilator
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.Convert
import Lean.Elab.Tactic.Omega

/-
The finite-state successor lemma is adapted from
boonsuan/nivat, revision 4e3614024227acd273c3e8ab41df92c2709e5ab0,
Nivat/TwoFactors/FiniteState.lean, periodic_of_deterministic_successor_bounded.

MIT License

Copyright (c) 2026 Boon Suan Ho

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

/-! Finite-state recurrence along all integer lines in one lattice direction. -/

set_option autoImplicit false

namespace D5.S1.Dynamics.Symbolic.KhetanFiniteRecurrence

open D5.S1.Dynamics.Symbolic.KhetanLaurent
open D5.S1.Dynamics.Symbolic.KhetanLaurent.Algebra

/-- A finite-range bilateral sequence with a uniquely determined successor has a positive period
bounded by its number of occurring states. Bilaterality makes the successor map surjective
on those states. Lemma 5.2 (`lem:finite-states`). -/
private theorem periodic_of_deterministic_successor_bounded {A : Type*} (s : ℤ → A)
    (hs : (Set.range s).Finite)
    (hdet : ∀ i j : ℤ, s i = s j → s (i + 1) = s (j + 1)) :
    ∃ p : ℕ, 0 < p ∧ p ≤ (Set.range s).ncard ∧ Function.Periodic s (p : ℤ) := by
  classical
  let : Fintype (Set.range s) := hs.fintype
  let t : ℤ → Set.range s := fun i => ⟨s i, i, rfl⟩
  let next : Set.range s → Set.range s := fun a => t (a.property.choose + 1)
  have hnext (i : ℤ) : next (t i) = t (i + 1) := by
    apply Subtype.ext
    exact hdet _ _ (t i).property.choose_spec
  have hsurj : Function.Surjective next := by
    rintro ⟨a, i, rfl⟩
    refine ⟨t (i - 1), ?_⟩
    simpa only [sub_add_cancel] using hnext (i - 1)
  have hinj : Function.Injective next := Finite.injective_iff_surjective.mpr hsurj
  have hprev (i j : ℤ) (h : t i = t j) : t (i - 1) = t (j - 1) := by
    apply hinj
    simpa only [hnext, sub_add_cancel] using h
  have hiter (n : ℕ) (i : ℤ) : next^[n] (t i) = t (i + (n : ℤ)) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hnext]
      congr 1
      push_cast
      ring
  let p := Function.minimalPeriod next (t 0)
  have hp : 0 < p :=
    Function.minimalPeriod_pos_of_mem_periodicPts (hinj.mem_periodicPts (t 0))
  have hzero : t (p : ℤ) = t 0 := by
    simpa only [hiter, zero_add] using
      (Function.isPeriodicPt_minimalPeriod next (t 0)).eq
  have hperiod (i : ℤ) : t (i + (p : ℤ)) = t i := by
    induction i using Int.induction_on with
    | zero => simpa using hzero
    | succ i hi =>
      simpa only [hnext, add_right_comm _ (1 : ℤ)] using congrArg next hi
    | pred i hi =>
      simpa only [sub_eq_add_neg, add_right_comm _ (-(1 : ℤ))] using hprev _ _ hi
  refine ⟨p, hp, ?_, fun i => congrArg Subtype.val (hperiod i)⟩
  simpa only [Set.ncard_eq_toFinset_card', Set.toFinset_card] using
    (Function.minimalPeriod_le_card (f := next) (x := t 0))

/-- The same recurrence acts on every line. Its finite-state bound depends only
on the global alphabet and the order, so one factorial is a global period. -/
theorem directional_recurrence_uniform_period {R : Type*} [CommRing R] [IsDomain R]
    (h : Configuration R) (hh : FiniteRange h) (u : Lattice)
    (r : ℕ) (a : ℕ → R) (ha : a r ≠ 0)
    (hrec : ∀ x : Lattice,
      ∑ j ∈ Finset.range (r + 1), a j * h (x + (j : ℤ) • u) = 0) :
    IsPeriod h (((Set.range h).ncard ^ (r + 1)).factorial • u) := by
  classical
  let : Fintype (Set.range h) := hh.fintype
  let B : ℕ := (Set.range h).ncard ^ (r + 1)
  intro x
  let seq : ℤ → R := fun i => h (x + i • u)
  let state : ℤ → (Fin (r + 1) → Set.range h) := fun i j =>
    ⟨seq (i + (j : ℕ)), x + (i + (j : ℕ)) • u, rfl⟩
  have hline (i : ℤ) :
      ∑ k ∈ Finset.range (r + 1), a k * seq (i + (k : ℕ)) = 0 := by
    simpa only [seq, add_zsmul, add_assoc] using hrec (x + i • u)
  have hdet : ∀ i j : ℤ, state i = state j → state (i + 1) = state (j + 1) := by
    intro i j hij
    have hletters (k : Fin (r + 1)) : seq (i + (k : ℕ)) = seq (j + (k : ℕ)) :=
      congrArg (fun s => (s k).val) hij
    have hnew : seq (i + 1 + (r : ℕ)) = seq (j + 1 + (r : ℕ)) := by
      have hi := hline (i + 1)
      have hj := hline (j + 1)
      rw [Finset.sum_range_succ] at hi hj
      have hs : (∑ k ∈ Finset.range r, a k * seq (i + 1 + (k : ℕ))) =
          ∑ k ∈ Finset.range r, a k * seq (j + 1 + (k : ℕ)) := by
        apply Finset.sum_congr rfl
        intro k hk
        congr 1
        convert hletters ⟨k + 1, by simpa using Finset.mem_range.mp hk⟩ using 1 <;>
          push_cast <;> congr 1 <;> ring
      rw [← hs] at hj
      exact mul_left_cancel₀ ha (add_left_cancel (hi.trans hj.symm))
    funext k
    apply Subtype.ext
    change seq (i + 1 + (k : ℕ)) = seq (j + 1 + (k : ℕ))
    by_cases hk : (k : ℕ) < r
    · convert hletters ⟨(k : ℕ) + 1, by omega⟩ using 1 <;>
        push_cast <;> congr 1 <;> ring
    · have heq : (k : ℕ) = r := by omega
      simpa only [heq] using hnew
  obtain ⟨p, hp, hb, hper⟩ := periodic_of_deterministic_successor_bounded state
    (Set.toFinite _) hdet
  have hbound : p ≤ B := by
    apply hb.trans
    calc
      (Set.range state).ncard ≤ Nat.card (Fin (r + 1) → Set.range h) := Set.ncard_le_card _
      _ = B := by simp [B, Nat.card_eq_fintype_card]
  have hseq : Function.Periodic seq (p : ℤ) := by
    intro i
    have he := congrArg (fun s => (s (0 : Fin (r + 1))).val) (hper i)
    simpa only [state, Fin.val_zero, Nat.cast_zero, add_zero] using he
  obtain ⟨m, hm⟩ := Nat.dvd_factorial hp hbound
  have he := hseq.nat_mul m 0
  have hmul : (m : ℤ) * (p : ℤ) = (B.factorial : ℤ) := by
    rw [hm, Nat.cast_mul, mul_comm]
  rw [hmul] at he
  change h (x + B.factorial • u) = h x
  simpa only [seq, zero_add, zero_smul, add_zero, natCast_zsmul] using he

end D5.S1.Dynamics.Symbolic.KhetanFiniteRecurrence
