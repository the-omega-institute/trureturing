/- GID: D5/S1/Words/Forbidden/NaimiCyclicWordReplacement
   generality: I
   mirror-B: D5/B/S1/Words/Forbidden/NaimiCyclicWordReplacement
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: [mathlib/module/Mathlib.Data.Fin.VecNotation, mathlib/module/Mathlib.Data.Fintype.Basic, mathlib/module/Mathlib.Data.List.OfFn, mathlib/module/Mathlib.Logic.Equiv.Defs, mathlib/module/Mathlib.Tactic.FinCases]
   utility: kind=certified-instance; basis=refutes=gid:D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.claim; result=D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.result; claim=D5/S1/Words/Forbidden/NaimiCyclicWordReplacement.claim
   digest: Four adjacent-compatible patterns cannot be rotated at their original starts in a finite linear host. -/

import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.FinCases

/-!
Ramin Naimi asks about cyclic replacement in the opening paragraph of
Section 8 of *Swapping Compatible Words* (arXiv:2610.31967v2, PDF p. 33).
The counterexample below uses the conventions in Section 2.1 and the
[same-position swap definition in Section 2.3, PDF p. 5](https://arxiv.org/html/2610.31967v2#S2.SS3.p4.1).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace NaimiCyclicWordReplacement

private def nextIndex {n : Nat} (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ (Nat.zero_lt_of_lt i.isLt)⟩

private def borderLength {a m : Nat} (p q : Fin m → Fin a) (k : Fin (m + 1)) : Prop :=
  (List.ofFn p).drop (m - k.val) = (List.ofFn q).take k.val

private def adjacentCompatible {a n m : Nat} (p : Fin n → Fin m → Fin a) : Prop :=
  ∀ (i : Fin n) (k : Fin (m + 1)),
    (borderLength (p i) (p i) k ↔ borderLength (p (nextIndex i)) (p (nextIndex i)) k) ∧
    (borderLength (p i) (p (nextIndex i)) k ↔ borderLength (p (nextIndex i)) (p i) k)

private def occursAt {a m L : Nat} (w : Fin L → Fin a) (p : Fin m → Fin a)
    (start : Nat) : Prop :=
  0 < m ∧ ∃ bound : start + m ≤ L, ∀ j : Fin m,
    w ⟨start + j.val, Nat.lt_of_lt_of_le (Nat.add_lt_add_left j.isLt start) bound⟩ = p j

/-- Every adjacent-compatible cycle admits a bijection that rotates all labeled
occurrences at their original starts in finite linear hosts. -/
def claim : Prop :=
  ∀ (a n m : Nat), 3 ≤ n → ∀ p : Fin n → Fin m → Fin a, adjacentCompatible p →
    ∀ L : Nat, ∃ Φ : (Fin L → Fin a) ≃ (Fin L → Fin a),
      ∀ (w : Fin L → Fin a) (i : Fin n) (start : Nat),
        occursAt w (p i) start ↔ occursAt (Φ w) (p (nextIndex i)) start

private def patterns : Fin 4 → Fin 3 → Fin 3 :=
  ![![0, 0, 1], ![0, 0, 2], ![0, 1, 1], ![0, 2, 1]]

private def host : Fin 4 → Fin 3 := ![0, 0, 2, 1]

/-- The adjacent-compatible cycle `001, 002, 011, 021` on host `0021`
demands two incompatible letters at output coordinate one. -/
theorem result : Not claim := by
  have borderTable (i j k : Fin 4) :
      borderLength (patterns i) (patterns j) k ↔
        k = 0 ∨ (i = j ∧ k = 3) ∨ (((i = 0 ∧ j = 2) ∨ (i = 1 ∧ j = 3)) ∧ k = 2) := by
    fin_cases i <;> fin_cases j <;> fin_cases k <;> unfold borderLength <;> decide
  -- The forward edges all have the same directed border set {0}.
  have cycleBorders (i k : Fin 4) :
      (borderLength (patterns i) (patterns i) k ↔ k = 0 ∨ k = 3) ∧
      (borderLength (patterns i) (patterns (nextIndex i)) k ↔ k = 0) ∧
      (borderLength (patterns (nextIndex i)) (patterns i) k ↔ k = 0) := by
    rw [borderTable i i k, borderTable i (nextIndex i) k, borderTable (nextIndex i) i k]
    fin_cases i <;> fin_cases k <;> decide
  have compatible : adjacentCompatible patterns := by
    intro i k
    exact ⟨(cycleBorders i k).1.trans (cycleBorders (nextIndex i) k).1.symm,
      (cycleBorders i k).2.1.trans (cycleBorders i k).2.2.symm⟩
  intro replace
  obtain ⟨replacement, exactAt⟩ := replace 3 4 3 (by decide) patterns compatible 4
  have first : occursAt host (patterns 1) 0 := by
    refine ⟨by decide, by decide, ?_⟩
    intro j
    fin_cases j <;> rfl
  have second : occursAt host (patterns 3) 1 := by
    refine ⟨by decide, by decide, ?_⟩
    intro j
    fin_cases j <;> rfl
  obtain ⟨_, firstLetters⟩ := ((exactAt host 1 0).mp first).2
  obtain ⟨_, secondLetters⟩ := ((exactAt host 3 1).mp second).2
  have left : replacement host (1 : Fin 4) = 1 := firstLetters (1 : Fin 3)
  have right : replacement host (1 : Fin 4) = 0 := secondLetters (0 : Fin 3)
  have unequal : (1 : Fin 3) ≠ 0 := by decide
  exact unequal (left.symm.trans right)

end NaimiCyclicWordReplacement
