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

attribute [local instance] Classical.propDecidable

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
    simp only [List.length_cons, decrements, List.countP_cons, decide_eq_true_eq,
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
  · have he : w = [] := by simpa [FirstZero, hz] using hw
    simp [he]
  · rw [FirstZero, if_neg hz] at hw
    have hh : 0 < h := by omega
    have hd : 0 < d := by omega
    have hlen : 0 < w.length := by
      by_contra hn
      have he : w = [] := List.eq_nil_of_length_eq_zero (by omega)
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
      calc
        _ = d * ((h - 1) + 1) := by ring
        _ = d * h := by rw [Nat.sub_add_cancel hh]
    omega



/-- Number of internal words of a specified length with each row budget at most `m`. -/
noncomputable def internal_words (d m t : ℕ) : ℕ :=
  MatharA379464Counting.count (Step d) t (fun w => ∀ i, decrements w i ≤ m)

private abbrev Rows (k m : ℕ) := {s : Finset (Fin k) // s.card ≤ m}

private theorem rows_card (k m : ℕ) :
    Fintype.card (Rows k m) = ∑ r ∈ Finset.range (m + 1), k.choose r := by
  classical
  let e : Rows k m ≃ (Σ r : Fin (m + 1), {s : Finset (Fin k) // s.card = r.val}) :=
    { toFun := fun s => ⟨⟨s.val.card, by omega⟩, ⟨s.val, rfl⟩⟩
      invFun := fun r => ⟨r.2.val, by have := r.2.property; have := r.1.isLt; omega⟩
      left_inv := by intro s; rfl
      right_inv := by rintro ⟨⟨r, hr⟩, ⟨s, hs⟩⟩; cases hs; rfl }
  simpa only [Fintype.card_sigma, Fintype.card_finset_len, Fintype.card_fin,
    Fin.sum_univ_eq_sum_range] using Fintype.card_congr e

private noncomputable def columnEquiv (d : ℕ) : Option (Step d) ≃ Finset (Fin d) where
  toFun o := match o with | none => ∅ | some s => s.val
  invFun s := if hs : s.Nonempty then some ⟨s, hs⟩ else none
  left_inv o := by
    cases o with
    | none => simp
    | some s => simp [s.property]
  right_inv s := by
    by_cases hs : s.Nonempty
    · simp [hs]
    · simp [hs, Finset.not_nonempty_iff_eq_empty.mp hs]

private theorem countP_ofFn {α : Type} {k : ℕ} (w : Fin k → α) (p : α → Bool) :
    (List.ofFn w).countP p = (Finset.univ.filter fun j => p (w j)).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.countP_cons, Fin.card_filter_univ_succ]
    rw [ih]
    split_ifs <;> omega

private theorem erase_decrements {d : ℕ} (l : List (Option (Step d))) (i : Fin d) :
    decrements (l.filterMap id) i = l.countP (fun o => decide (i ∈ columnEquiv d o)) := by
  induction l with
  | nil => simp [decrements]
  | cons o l ih =>
    cases o with
    | none => simpa [columnEquiv, decrements] using ih
    | some s =>
      by_cases hs : i ∈ s.val
      · simpa [columnEquiv, decrements, List.countP_cons, hs] using congrArg Nat.succ ih
      · simpa [columnEquiv, decrements, List.countP_cons, hs] using ih


private noncomputable def columnRowsEquiv (d k m : ℕ) :
    {w : Fin k → Option (Step d) //
      ∀ i, decrements ((List.ofFn w).filterMap id) i ≤ m} ≃ (Fin d → Rows k m) := by
  classical
  let col (w : Fin k → Option (Step d)) (i : Fin d) : Finset (Fin k) :=
    Finset.univ.filter (fun j => i ∈ columnEquiv d (w j))
  have hcount (w : Fin k → Option (Step d)) (i : Fin d) :
      decrements ((List.ofFn w).filterMap id) i = (col w i).card := by
    rw [erase_decrements, countP_ofFn]
    simp only [col, decide_eq_true_eq]
  refine
    { toFun := fun w i => ⟨col w.val i, by rw [← hcount]; exact w.property i⟩
      invFun := fun rows => ⟨(fun j => (columnEquiv d).symm
        (Finset.univ.filter fun i => j ∈ (rows i).val)), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro i
    rw [hcount]
    convert (rows i).property using 1
    congr 1
    ext j
    simp [col]
  · intro w
    apply Subtype.ext
    funext j
    apply (columnEquiv d).injective
    simp only [Equiv.apply_symm_apply]
    ext i
    simp [col]
  · intro rows
    funext i
    apply Subtype.ext
    ext j
    simp [col]

/-- Row budgets are the binomial transform of words with no empty columns. -/
theorem insertion_identity (d m k : ℕ) :
    (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      ∑ t ∈ Finset.range (k + 1), k.choose t * internal_words d m t := by
  classical
  have hc := Fintype.card_congr (columnRowsEquiv d k m)
  have hi := MatharA379464Counting.insertion_formula (Step d) k
    (fun w => ∀ i, decrements w i ≤ m)
  rw [Fintype.card_fun, rows_card, Fintype.card_fin] at hc
  have hcount : (∑ r ∈ Finset.range (m + 1), k.choose r) ^ d =
      MatharA379464Counting.count (Option (Step d)) k
        (fun l => ∀ i, decrements (l.filterMap id) i ≤ m) := by
    simpa only [MatharA379464Counting.count, ← Nat.card_eq_fintype_card] using hc.symm
  exact hcount.trans hi

end D5.S1.Words.LatticePaths.KotesovecA263160
