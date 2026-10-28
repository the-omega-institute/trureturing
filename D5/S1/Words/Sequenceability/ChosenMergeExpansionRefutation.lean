/- GID: D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation
   generality: I
   mirror-B: D5/B/S1/Words/Sequenceability/ChosenMergeExpansionRefutation
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=bounded-enumeration; basis=refutes=gid:D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.claim; result=D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.result; claim=D5/S1/Words/Sequenceability/ChosenMergeExpansionRefutation.claim
   digest: The fixed C2 x C4 forced-cut obstruction refutes the chosen-merge expansion route. -/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Permutation
import Mathlib.Tactic

/-! A fixed C₂ × C₄ forced-cut refutation of uniform chosen-merge expansion. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Sequenceability.ChosenMergeExpansionRefutation

abbrev G := ZMod 2 × ZMod 4

def Good (w : List G) : Prop :=
  ((List.finRange (w.length + 1)).all (fun i =>
    (List.finRange (w.length + 1)).all (fun j =>
      decide (i.1 < j.1 →
        (i.1 ≠ 0 ∨ j.1 ≠ w.length) →
          ((w.drop i.1).take (j.1 - i.1)).sum ≠ 0)))) = true

def expand (x y : G) (w : List G) : List G :=
  w.flatMap (fun z => if z = x + y then [x, y] else [z])

def claim : Prop :=
  ∀ (A : Finset G), 0 ∉ A → 3 ≤ A.card →
    ∀ a b : G, a ∈ A → b ∈ A → a ≠ b → a + b ∉ insert 0 A →
      ((∃ w : List G,
          w.Perm (insert (a + b) ((A.erase a).erase b)).toList ∧ Good w) →
        ∃ w : List G,
          w.Perm (insert (a + b) ((A.erase a).erase b)).toList ∧ Good w ∧
            (Good (expand a b w) ∨ Good (expand b a w)))

private def p : G := (0, 1)
private def q : G := (0, 3)
private def r : G := (1, 0)
private def s : G := (1, 1)
private def t : G := (1, 3)
private def a : G := (0, 2)
private def b : G := (1, 2)

private def B : List G := [p, q, r, s, t]

set_option maxHeartbeats 1000000 in
private theorem forced_cut (w : List G) (hw : w.Perm B) (hgood : Good w) :
    w = [p, s, r, t, q] ∨ w = [q, t, r, s, p] ∨
      w = [s, p, r, q, t] ∨ w = [t, q, r, p, s] := by
  have hwlen : w.length = 5 := by simpa [B] using hw.length_eq
  have hwne : w ≠ [] := by
    intro h
    simp [h] at hwlen
  obtain ⟨x₁, w₁, rfl⟩ := List.exists_cons_of_ne_nil hwne
  have hw₁len : w₁.length = 4 := by simpa using hwlen
  have hw₁ne : w₁ ≠ [] := by
    intro h
    simp [h] at hw₁len
  obtain ⟨x₂, w₂, rfl⟩ := List.exists_cons_of_ne_nil hw₁ne
  have hw₂len : w₂.length = 3 := by simpa using hw₁len
  have hw₂ne : w₂ ≠ [] := by
    intro h
    simp [h] at hw₂len
  obtain ⟨x₃, w₃, rfl⟩ := List.exists_cons_of_ne_nil hw₂ne
  have hw₃len : w₃.length = 2 := by simpa using hw₂len
  have hw₃ne : w₃ ≠ [] := by
    intro h
    simp [h] at hw₃len
  obtain ⟨x₄, w₄, rfl⟩ := List.exists_cons_of_ne_nil hw₃ne
  have hw₄len : w₄.length = 1 := by simpa using hw₃len
  have hw₄ne : w₄ ≠ [] := by
    intro h
    simp [h] at hw₄len
  obtain ⟨x₅, w₅, rfl⟩ := List.exists_cons_of_ne_nil hw₄ne
  have hw₅len : w₅.length = 0 := by simpa using hw₄len
  cases w₅ with
  | nil =>
    have hx₁ : x₁ ∈ B := (hw.mem_iff).mp (by simp)
    have hx₂ : x₂ ∈ B := (hw.mem_iff).mp (by simp)
    have hx₃ : x₃ ∈ B := (hw.mem_iff).mp (by simp)
    have hx₄ : x₄ ∈ B := (hw.mem_iff).mp (by simp)
    have hx₅ : x₅ ∈ B := (hw.mem_iff).mp (by simp)
    have hnodup : ([x₁, x₂, x₃, x₄, x₅] : List G).Nodup :=
      (hw.nodup_iff).2 (by decide +kernel)
    simp [B] at hx₁ hx₂ hx₃ hx₄ hx₅
    rcases hx₁ with rfl | rfl | rfl | rfl | rfl
    all_goals try simp_all [List.nodup_cons]
    all_goals rcases hx₂ with rfl | rfl | rfl | rfl | rfl
    all_goals try simp_all [List.nodup_cons]
    all_goals rcases hx₃ with rfl | rfl | rfl | rfl | rfl
    all_goals try simp_all [List.nodup_cons]
    all_goals rcases hx₄ with rfl | rfl | rfl | rfl | rfl
    all_goals try simp_all [List.nodup_cons]
    all_goals rcases hx₅ with rfl | rfl | rfl | rfl | rfl
    all_goals try { exfalso; simpa using hnodup }
    all_goals revert hgood
    all_goals simp only [Good]
    all_goals decide +kernel
  | cons head tail => simp_all

private theorem bad₁ : ¬ Good (expand a b [p, s, r, t, q]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₂ : ¬ Good (expand b a [p, s, r, t, q]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₃ : ¬ Good (expand a b [q, t, r, s, p]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₄ : ¬ Good (expand b a [q, t, r, s, p]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₅ : ¬ Good (expand a b [s, p, r, q, t]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₆ : ¬ Good (expand b a [s, p, r, q, t]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₇ : ¬ Good (expand a b [t, q, r, p, s]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

private theorem bad₈ : ¬ Good (expand b a [t, q, r, p, s]) := by
  simp only [expand, p, q, r, s, t, a, b]
  simp only [Good]
  decide +kernel

theorem result : Not claim := by
  let A : Finset G := {p, q, s, t, a, b}
  have hA0 : (0 : G) ∉ A := by decide +kernel
  have hAc : 3 ≤ A.card := by decide +kernel
  have hap : a ∈ A := by decide +kernel
  have hbp : b ∈ A := by decide +kernel
  have hab : a ≠ b := by decide +kernel
  have hlegal : a + b ∉ insert (0 : G) A := by decide +kernel
  have hBset : insert (a + b) ((A.erase a).erase b) = B.toFinset := by
    have habsum : a + b = r := by decide +kernel
    rw [habsum]
    ext x
    rcases x with ⟨x₁, x₂⟩
    fin_cases x₁ <;> fin_cases x₂ <;>
      simp [A, B, p, q, r, s, t, a, b] <;> decide
  have hBnodup : B.Nodup := by decide +kernel
  have hBperm : B.Perm (insert (a + b) ((A.erase a).erase b)).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq hBnodup
      (Finset.nodup_toList _)
    simpa [hBset]
  have horder : [p, s, r, t, q].Perm B := by decide +kernel
  have hgoodB : Good [p, s, r, t, q] := by
    simp only [Good]
    decide +kernel
  intro hclaim
  obtain ⟨w, hw, hgood, hexpand⟩ :=
    hclaim A hA0 hAc a b hap hbp hab hlegal
      ⟨[p, s, r, t, q], horder.trans hBperm, hgoodB⟩
  have hwB : w.Perm B := by
    apply hw.trans
    exact (hBperm.symm.trans (List.Perm.refl _))
  obtain h₁ | h₂ | h₃ | h₄ := forced_cut w hwB hgood
  · subst w
    exact Or.elim hexpand bad₁ bad₂
  · subst w
    exact Or.elim hexpand bad₃ bad₄
  · subst w
    exact Or.elim hexpand bad₅ bad₆
  · subst w
    exact Or.elim hexpand bad₇ bad₈

#print axioms result

end D5.S1.Words.Sequenceability.ChosenMergeExpansionRefutation
