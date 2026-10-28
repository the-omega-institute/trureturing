/- GID: D5/S0/Computability/BinaryMachine/TapeEquiv
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/TapeEquiv
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Licensed finite binary machine TapeEquiv supply. -/

module

/-
Licensed content port from RBarish-UTokyo/NPCompleteness-Lean4,
immutable revision 3e603e795b44fedcf7d6dd65b7d1e30547ead925, Complexity/TapeEquiv.lean.
Apache-2.0; full license and finite replacement contract:
docs/reports/licenses/RBarishBinaryMachine.md and RBarishBinaryMachine-LICENSE.txt.
Only module imports and this repository header are adapted.
-/

public import D5.S0.Computability.BinaryMachine.Machine

/-!
The zipper representation permits redundant trailing blank cells. This module
identifies representations having the same blank-padded symbols at every offset
from the head. Every machine operation and bounded run respects this relation.
-/

@[expose] public section

namespace Complexity

/-- Equality of finite lists regarded as infinite blank-padded symbol streams. -/
def BlankEq (xs ys : List Symbol) : Prop :=
  ∀ n, xs.getD n .blank = ys.getD n .blank

namespace BlankEq

theorem refl (xs : List Symbol) : BlankEq xs xs := fun _ => rfl

theorem symm {xs ys : List Symbol} (h : BlankEq xs ys) : BlankEq ys xs :=
  fun n => (h n).symm

theorem trans {xs ys zs : List Symbol} (h : BlankEq xs ys) (h' : BlankEq ys zs) :
    BlankEq xs zs := fun n => (h n).trans (h' n)

theorem head {xs ys : List Symbol} (h : BlankEq xs ys) :
    xs.headD .blank = ys.headD .blank := by
  simpa only [List.headD_eq_getD] using h 0

theorem drop_one {xs ys : List Symbol} (h : BlankEq xs ys) :
    BlankEq (xs.drop 1) (ys.drop 1) := by
  intro n
  have hn := h (n + 1)
  cases xs <;> cases ys
  · rfl
  · simpa [List.getD_cons_succ] using hn
  · simpa [List.getD_cons_succ] using hn
  · simpa [List.getD_cons_succ] using hn

theorem cons {xs ys : List Symbol} (h : BlankEq xs ys) (a : Symbol) :
    BlankEq (a :: xs) (a :: ys) := by
  intro n
  cases n with
  | zero => rfl
  | succ n => simpa only [List.getD_cons_succ] using h n

theorem replicate_blank (n : Nat) : BlankEq (List.replicate n .blank) [] := by
  induction n with
  | zero => exact refl []
  | succ n ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      simpa only [List.replicate_succ, List.getD_cons_succ, List.getD_nil]
        using ih i

theorem append_blanks (xs : List Symbol) (n : Nat) :
    BlankEq (xs ++ List.replicate n .blank) xs := by
  induction xs with
  | nil => exact replicate_blank n
  | cons a xs ih => exact ih.cons a

theorem bits {xs ys : List Symbol} (h : BlankEq xs ys) :
    Tape.bits xs = Tape.bits ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons y ys =>
      have hh : Symbol.blank = y := by
        simpa only [List.getD_nil, List.getD_cons_zero] using h 0
      subst y
      rfl
  | cons x xs ih =>
    cases ys with
    | nil =>
      have hh : x = Symbol.blank := by
        simpa only [List.getD_nil, List.getD_cons_zero] using h 0
      subst x
      rfl
    | cons y ys =>
      have hh : x = y := by
        simpa only [List.getD_cons_zero] using h 0
      subst y
      have ht : BlankEq xs ys := by
        intro n
        simpa only [List.getD_cons_succ] using h (n + 1)
      cases x with
      | blank => rfl
      | sep => rfl
      | bit b => exact congrArg (List.cons b) (ih ht)

end BlankEq

namespace Tape

/-- The tapes agree at every offset from their heads; explicit trailing blanks
and implicit trailing blanks have the same meaning. -/
def Equivalent (t u : Tape) : Prop :=
  BlankEq t.left u.left ∧ BlankEq t.right u.right

/-- Materialize additional blank cells at the far end of each tape half. -/
def pad (t : Tape) (leftPadding rightPadding : Nat) : Tape :=
  ⟨t.left ++ List.replicate leftPadding .blank,
   t.right ++ List.replicate rightPadding .blank⟩

theorem pad_equivalent (t : Tape) (leftPadding rightPadding : Nat) :
    (t.pad leftPadding rightPadding).Equivalent t :=
  ⟨BlankEq.append_blanks _ _, BlankEq.append_blanks _ _⟩

namespace Equivalent

theorem refl (t : Tape) : Equivalent t t := ⟨BlankEq.refl _, BlankEq.refl _⟩

theorem symm {t u : Tape} (h : Equivalent t u) : Equivalent u t :=
  ⟨h.1.symm, h.2.symm⟩

theorem trans {t u v : Tape} (h : Equivalent t u) (h' : Equivalent u v) :
    Equivalent t v := ⟨h.1.trans h'.1, h.2.trans h'.2⟩

theorem read {t u : Tape} (h : Equivalent t u) : t.read = u.read := h.2.head

theorem write {t u : Tape} (h : Equivalent t u) (a : Symbol) :
    Equivalent (t.write a) (u.write a) :=
  ⟨h.1, h.2.drop_one.cons a⟩

end Equivalent

theorem move_left_eq (t : Tape) :
    t.move .left = ⟨t.left.drop 1, t.left.headD .blank :: t.right⟩ := by
  cases t with
  | mk left right => cases left <;> rfl

theorem move_right_eq (t : Tape) :
    t.move .right = ⟨t.right.headD .blank :: t.left, t.right.drop 1⟩ := by
  cases t with
  | mk left right => cases right <;> rfl

namespace Equivalent

theorem move {t u : Tape} (h : Equivalent t u) (d : Move) :
    Equivalent (t.move d) (u.move d) := by
  cases d with
  | stay => exact h
  | left =>
    rw [move_left_eq, move_left_eq]
    refine ⟨h.1.drop_one, ?_⟩
    change BlankEq (t.left.headD .blank :: t.right) (u.left.headD .blank :: u.right)
    rw [h.1.head]
    exact h.2.cons _
  | right =>
    rw [move_right_eq, move_right_eq]
    refine ⟨?_, h.2.drop_one⟩
    change BlankEq (t.right.headD .blank :: t.left) (u.right.headD .blank :: u.left)
    rw [h.2.head]
    exact h.1.cons _

theorem output {t u : Tape} (h : Equivalent t u) : t.output = u.output := h.2.bits

end Equivalent

end Tape

/-- Agreement of bounded-run observations, including exhaustion of the bound,
the Boolean halting decision, and the contents of the infinite tape. -/
def ResultEquivalent : Option (Bool × Tape) → Option (Bool × Tape) → Prop
  | none, none => True
  | some (b, t), some (b', t') => b = b' ∧ t.Equivalent t'
  | _, _ => False

/-- Replacing explicit trailing blanks by implicit blanks does not affect any
bounded computation, and does not alter the instruction count. -/
theorem run_equivalent (M : Machine) (fuel : Nat) (q : Fin (M.states + 1))
    (t u : Tape) (h : t.Equivalent u) :
    ResultEquivalent (run M fuel ⟨q, t⟩) (run M fuel ⟨q, u⟩) := by
  induction fuel generalizing q t u with
  | zero => trivial
  | succ fuel ih =>
    simp only [run]
    rw [← h.read]
    cases hcode : M.code q t.read with
    | halt b => exact ⟨rfl, h⟩
    | step a d q' => exact ih q' _ _ ((h.write a).move d)

/-- A halting run on one representation also halts on an equivalent
representation within the identical bound, with the same decision and output. -/
theorem run_some_of_equivalent (M : Machine) (fuel : Nat)
    (q : Fin (M.states + 1)) (t u : Tape) (h : t.Equivalent u)
    (b : Bool) (t' : Tape) (hrun : run M fuel ⟨q, t⟩ = some (b, t')) :
    ∃ u', run M fuel ⟨q, u⟩ = some (b, u') ∧ t'.Equivalent u' := by
  have hres := run_equivalent M fuel q t u h
  rw [hrun] at hres
  cases hu : run M fuel ⟨q, u⟩ with
  | none => simp [hu, ResultEquivalent] at hres
  | some result =>
    obtain ⟨b', u'⟩ := result
    have hh : b = b' ∧ t'.Equivalent u' := by
      simpa only [hu, ResultEquivalent] using hres
    obtain ⟨rfl, heq⟩ := hh
    exact ⟨u', rfl, heq⟩

end Complexity
