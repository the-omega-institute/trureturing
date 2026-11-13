/- GID: D5/S1/Words/LatticePaths/KotesovecA263160
   generality: I
   mirror-B: D5/B/S1/Words/LatticePaths/KotesovecA263160
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: First-zero lattice paths and the diagonal OEIS A263160 limit. -/

/-
Source: OEIS A263160 revision 21 and A263159 revision 16.
Preregistration: https://github.com/the-omega-institute/trureturing/issues/29912.
The full root-limit conjecture remains open until a theorem proves it for the literal count.
Prospective admission_basis: open-problem-resolution for the full result;
escape-witness for independently admissible supporting counting content.
Definitions are bind-only and used by the counting statements. The prefix-budget
argument is content; direct applications of existing counting identities are
bind-only auxiliaries and must have actual mathematical consumers.
The statements are symbolic and unbounded; utility: none.
-/

import D5.S1.Words.LatticePaths.MatharA379464Counting
import Mathlib.Analysis.SumIntegralExpDecay
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Data.Nat.Choose.Bounds

open scoped BigOperators Topology
open Filter

set_option maxHeartbeats 1000000

namespace D5.S1.Words.LatticePaths.KotesovecA263160

/-- A labelled nonempty set of coordinates decremented by a single step. -/
abbrev Step (d : ℕ) := {s : Finset (Fin d) // s.Nonempty}

/-- Number of decrements of coordinate `i` in an ordered word. -/
def decrements {d : ℕ} (w : List (Step d)) (i : Fin d) : ℕ :=
  w.countP (fun s => decide (i ∈ s.val))

/-- The literal stopping rule, including the immediate empty path convention. -/
def FirstZero {d : ℕ} (h : ℕ) (w : List (Step d)) : Prop :=
  if h = 0 ∨ d = 0 then w = [] else
    (∀ r < w.length, ∀ i, decrements (w.take r) i < h) ∧
      ∃ i, decrements w i = h

/-- The finite count of literal first-zero paths from height `h` in `d` coordinates. -/
noncomputable def paths (d h : ℕ) : ℕ := by
  classical
  exact ∑ t ∈ Finset.range (d * h + 1),
    Fintype.card {w : Fin t → Step d // FirstZero h (List.ofFn w)}

/-- The main diagonal of the first-zero path array. -/
noncomputable def a (n : ℕ) : ℕ := paths n n

private theorem decrements_append {d : ℕ} (u v : List (Step d)) (i : Fin d) :
    decrements (u ++ v) i = decrements u i + decrements v i := by
  simp [decrements]

private theorem decrements_take_le {d : ℕ} (w : List (Step d)) (r : ℕ) (i : Fin d) :
    decrements (w.take r) i ≤ decrements w i := by
  have he := congrArg (fun l => decrements l i) (List.take_append_drop r w)
  rw [decrements_append] at he
  omega

private theorem length_le_total_decrements {d : ℕ} (w : List (Step d)) :
    w.length ≤ ∑ i, decrements w i := by
  induction w with
  | nil => simp [decrements]
  | cons s w ih =>
    have hs : 1 ≤ s.val.card := s.property.card_pos
    have hc : (∑ i : Fin d, if i ∈ s.val then 1 else 0) = s.val.card := by
      simp
    simp only [List.length_cons, decrements, List.countP_cons, Bool.decide_coe,
      Finset.sum_add_distrib]
    change w.length + 1 ≤ (∑ i : Fin d, decrements w i) +
      ∑ i : Fin d, if i ∈ s.val then 1 else 0
    rw [hc]
    omega

private theorem internal_length_bound {d m : ℕ} (w : List (Step d))
    (hw : ∀ i, decrements w i ≤ m) : w.length ≤ d * m := by
  calc
    w.length ≤ ∑ i, decrements w i := length_le_total_decrements w
    _ ≤ ∑ _ : Fin d, m := Finset.sum_le_sum (fun i _ => hw i)
    _ = d * m := by simp

/-- Every literal path lies in the finite length range used by `paths`. -/
theorem first_zero_length_bound {d h : ℕ} {w : List (Step d)}
    (hw : FirstZero h w) : w.length ≤ d * h := by
  by_cases hz : h = 0 ∨ d = 0
  · simpa [FirstZero, hz] using hw
  · rw [FirstZero, if_neg hz] at hw
    have hh : 0 < h := by omega
    have hd : 0 < d := by omega
    have hlen : 0 < w.length := by
      by_contra hn
      have he : w = [] := List.length_eq_zero.mp (by omega)
      rcases hw.2 with ⟨i, hi⟩
      simp [he, decrements] at hi
      omega
    have ht : ∀ i, decrements (w.take (w.length - 1)) i ≤ h - 1 := by
      intro i
      have := hw.1 (w.length - 1) (by omega) i
      omega
    have hb := internal_length_bound (w.take (w.length - 1)) ht
    simp only [List.length_take, min_eq_left (Nat.sub_le _ _)] at hb
    have hm : d * (h - 1) + d = d * h := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hh]
    omega

end D5.S1.Words.LatticePaths.KotesovecA263160
