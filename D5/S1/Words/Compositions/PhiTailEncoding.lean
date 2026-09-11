/- GID: D5/S1/Words/Compositions/PhiTailEncoding
   generality: G
   mirror-B: D5/B/S1/Words/Compositions/PhiTailEncoding
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Admissible permutations produce bounded reversed tail words. -/

import D5.S1.Words.Compositions.AlternatingResidualBridge
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace D5.S1.Words.Compositions.PhiTailEncoding

/-! The definitions below are the zero-based form of the A392714 source.
The admissibility predicate is repeated here so this module can be consumed
without importing a prose probe. -/

def suffixBudget (n k : ℕ) (p : Equiv.Perm (Fin (2 * n))) : ℤ :=
  ∑ i : Fin (2 * n), if 2 * n - k ≤ i.val then ((p i).val : ℤ) - (n : ℤ) else 0

def admissible (n : ℕ) (p : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i : Fin (2 * n), i.val = 0 → (p i).val = 0) ∧
    ∀ k ∈ Finset.Ico 1 (2 * n), 0 ≤ suffixBudget n k p

noncomputable def phi (n : ℕ) : Finset (Equiv.Perm (Fin (2 * n))) := by
  classical
  exact Finset.univ.filter (admissible n)

private def tailIndex {n : ℕ} (hn : 1 ≤ n) (j : Fin (2 * n - 1)) : Fin (2 * n) :=
  ⟨2 * n - 1 - j.val, by omega⟩

private def zeroFin {n : ℕ} (hn : 1 ≤ n) : Fin (2 * n) := ⟨0, by omega⟩

/-- The reversed tail, with the source's one-based shift removed. -/
def tailWord (n : ℕ) (p : Equiv.Perm (Fin (2 * n))) (hn : 1 ≤ n) :
    List ℤ :=
  List.ofFn (fun j : Fin (2 * n - 1) =>
    (p (tailIndex hn j)).val - (n : ℤ))

theorem tailWord_length (n : ℕ) (p : Equiv.Perm (Fin (2 * n))) (hn : 1 ≤ n) :
    (tailWord n p hn).length = 2 * n - 1 := by
  simp [tailWord]

private theorem tailIndex_ne_zero {n : ℕ} (hn : 1 ≤ n) (j : Fin (2 * n - 1)) :
    (tailIndex hn j).val ≠ 0 := by
  dsimp [tailIndex]
  omega

private theorem tailValue_ne_zero {n : ℕ} (p : Equiv.Perm (Fin (2 * n)))
    (hn : 1 ≤ n) (hp0 : p (zeroFin hn) = zeroFin hn) (i : Fin (2 * n))
    (hi : i.val ≠ 0) :
    (p i).val ≠ 0 := by
  intro h
  have hpi : p i = zeroFin hn := Fin.ext (by simpa [zeroFin] using h)
  have : i = zeroFin hn := p.injective (hpi.trans hp0.symm)
  exact hi (congrArg Fin.val this)

/-- Every reversed-tail letter lies in the intended residual alphabet interval.
This is the part of the Φ-to-word reduction that is independent of the
prefix inequalities. -/
theorem tailWord_entry_bounds {n : ℕ} (p : Equiv.Perm (Fin (2 * n)))
    (hn : 1 ≤ n) (hp0 : p (zeroFin hn) = zeroFin hn) (j : Fin (2 * n - 1)) :
    -(n : ℤ) < (p (tailIndex hn j)).val - (n : ℤ) ∧
      (p (tailIndex hn j)).val - (n : ℤ) < (n : ℤ) := by
  have hidx := tailIndex_ne_zero hn j
  have hval := tailValue_ne_zero p hn hp0 _ hidx
  have hvlt := (p (tailIndex hn j)).isLt
  constructor <;> omega

theorem mem_phi_tailWord_bounds {n : ℕ} {p : Equiv.Perm (Fin (2 * n))}
    (hp : p ∈ phi n) (hn : 1 ≤ n) (j : Fin (2 * n - 1)) :
    -(n : ℤ) < (p (tailIndex hn j)).val - (n : ℤ) ∧
      (p (tailIndex hn j)).val - (n : ℤ) < (n : ℤ) := by
  classical
  have hp0 : p (zeroFin hn) = zeroFin hn := by
    have hp' : p ∈ Finset.univ.filter (admissible n) := by simpa [phi] using hp
    have h := (Finset.mem_filter.mp hp').2
    have hz := h.1 (zeroFin hn) rfl
    exact Fin.ext (by simpa [zeroFin] using hz)
  exact tailWord_entry_bounds p hn hp0 j

end D5.S1.Words.Compositions.PhiTailEncoding
