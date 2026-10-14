/- Independent static candidate. No compile or replay acceptance is asserted.
The decoded domain remains exactly Fin 20 → Option (Fin 4); no unknown image
is accepted. The checker retains fuel zero rejection and all four children.
Only a prefix whose pivot is already known uses the shorter Fin pivot loop.
-/

import D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false

namespace D5.S3.Quantum.Entanglement.EJM.EJMCompactDominates

open D5.S3.Quantum.Entanglement.EJM.EJMCompactPartial
open D5.S3.Quantum.Entanglement.EJM.EJMGlobalScoreSymmetry (GlobalSym Cut dominates)
open D5.S3.Quantum.Entanglement.EJM.EJMScoreSymmetry (sourceSymmetry)
open D5.S3.Quantum.Entanglement.EJM.EJMPartialBoundData (outcome)
open D5.S0.Certificates.FiniteSymmetryBoundReplay (Partial)

def value (q : PackedPartial) (j : Coord) : Value :=
  ⟨q.digits / base ^ j.val % base, Nat.mod_lt _ (by decide : 0 < base)⟩

private theorem decode_value (q : PackedPartial) (j : Coord)
    (hj : j.val < q.depth) : decode q j = some (value q j) := by
  exact decode_known q j hj

/- A definitionally identical copy provides access to the original private
prefix helper. Its equality is consumed by the whole-checker bridge. -/
private def originalPrefix (s : GlobalSym) (p : Partial Coord Value) (j : Coord) : Bool :=
  if sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v then true
  else match p (sourceSymmetry s.1 j), p j with
    | some a, some b => decide (outcome s.2 a = b)
    | _, _ => false

private theorem dominates_formula (s : Cut) (p : Partial Coord Value) :
    dominates s p =
      (match p (sourceSymmetry s.1.1 s.2), p s.2 with
      | some a, some b => decide (outcome s.1.2 a < b ∧
          ∀ j, j < s.2 → originalPrefix s.1 p j = true)
      | _, _ => false) := rfl

def prefixAt (s : GlobalSym) (q : PackedPartial) (j : Coord) : Bool :=
  if (sourceSymmetry s.1 j).val < q.depth then
    decide (outcome s.2 (value q (sourceSymmetry s.1 j)) = value q j)
  else false

private theorem prefixAt_eq (s : GlobalSym) (q : PackedPartial) (j : Coord)
    (hj : j.val < q.depth) :
    prefixAt s q j = originalPrefix s (decode q) j := by
  by_cases hi : (sourceSymmetry s.1 j).val < q.depth
  · by_cases fixed : sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v
    · have hsame : outcome s.2 (value q j) = value q j := fixed.2 _
      simp [prefixAt, originalPrefix, fixed, fixed.1, fixed.2, hj]
    · simp only [prefixAt, hi, if_pos, originalPrefix, fixed, if_false,
        decode_value q (sourceSymmetry s.1 j) hi, decode_value q j hj]
  · have notFixed : ¬ (sourceSymmetry s.1 j = j ∧ ∀ v, outcome s.2 v = v) := by
      intro fixed
      apply hi
      simpa only [fixed.1] using hj
    have hnone : decode q (sourceSymmetry s.1 j) = none :=
      decode_unknown q _ (Nat.le_of_not_gt hi)
    simp only [prefixAt, hi, if_false, originalPrefix, notFixed, if_false, hnone]

def prefixIndex (pivot : Coord) (j : Fin pivot.val) : Coord :=
  ⟨j.val, Nat.lt_trans j.isLt pivot.isLt⟩

private theorem prefix_all_iff (s : GlobalSym) (q : PackedPartial) (pivot : Coord)
    (hp : pivot.val < q.depth) :
    (∀ j : Fin pivot.val, prefixAt s q (prefixIndex pivot j) = true) ↔
      (∀ j : Coord, j < pivot → originalPrefix s (decode q) j = true) := by
  constructor
  · intro h j hj
    let k : Fin pivot.val := ⟨j.val, hj⟩
    have hk : prefixIndex pivot k = j := Fin.ext rfl
    have hknown : j.val < q.depth := Nat.lt_trans hj hp
    have hlocal := h k
    rw [hk, prefixAt_eq s q j hknown] at hlocal
    exact hlocal
  · intro h j
    have hj : prefixIndex pivot j < pivot := j.isLt
    have hknown : (prefixIndex pivot j).val < q.depth := Nat.lt_trans j.isLt hp
    rw [prefixAt_eq s q (prefixIndex pivot j) hknown]
    exact h _ hj

def dominatesPacked (s : Cut) (q : PackedPartial) : Bool :=
  if s.2.val < q.depth then
    if (sourceSymmetry s.1.1 s.2).val < q.depth then
      decide (outcome s.1.2 (value q (sourceSymmetry s.1.1 s.2)) < value q s.2 ∧
        ∀ j : Fin s.2.val, prefixAt s.1 q (prefixIndex s.2 j) = true)
    else false
  else false

/- The bound retains the original complete coordinate domain. The stronger
prefix fact used in the proof is j < pivot < depth, not an assumption that
any unknown transformed coordinate has a value. -/
theorem dominatesPacked_eq_original (s : Cut) (q : PackedPartial) :
    dominatesPacked s q = dominates s (decode q) := by
  rw [dominates_formula]
  by_cases hp : s.2.val < q.depth
  · by_cases hi : (sourceSymmetry s.1.1 s.2).val < q.depth
    · simp only [dominatesPacked, hp, hi, if_pos,
        decode_value q (sourceSymmetry s.1.1 s.2) hi, decode_value q s.2 hp]
      apply decide_eq_decide.mpr
      exact and_congr Iff.rfl (prefix_all_iff s.1 q s.2 hp)
    · have hnone : decode q (sourceSymmetry s.1.1 s.2) = none :=
        decode_unknown q _ (Nat.le_of_not_gt hi)
      simp only [dominatesPacked, hp, hi, if_pos, if_false, hnone]
  · have hnone : decode q s.2 = none := decode_unknown q _ (Nat.le_of_not_gt hp)
    simp only [dominatesPacked, hp, if_false, hnone]
    cases decode q (sourceSymmetry s.1.1 s.2) <;> rfl

def checkFast {Cache : Type}
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ) (gap : ℤ) :
    ℕ → Fin EJMGlobalDAGData.Size → Cache → PackedPartial → Bool
  | 0, _, _, _ => false
  | fuel + 1, index, cache, q =>
    match EJMGlobalDAGData.nodes (fuel + 1) index with
    | .bound => decide (gap ≤ lower cache)
    | .symmetry s => dominatesPacked s q
    | .split i children => decide (∀ a,
        checkFast step lower gap fuel (children a)
          (step cache i a) (advance fuel q i a) = true)

theorem checkFast_eq_checkPacked {Cache : Type}
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ) (gap : ℤ)
    (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size) (cache : Cache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    checkFast step lower gap fuel index cache q =
      checkPacked EJMGlobalDAGData.nodes step lower dominates gap fuel index cache q := by
  induction fuel generalizing index cache q with
  | zero => rfl
  | succ fuel ih =>
    cases hn : EJMGlobalDAGData.nodes (fuel + 1) index with
    | bound => simp only [checkFast, checkPacked, hn]
    | symmetry s =>
      simp only [checkFast, checkPacked, hn]
      exact dominatesPacked_eq_original s q
    | split i children =>
      simp only [checkFast, checkPacked, hn]
      cases fuel with
      | zero => simp [advance, checkFast, checkPacked]
      | succ fuel =>
        have hchild (a : Value) :
            checkFast step lower gap (fuel + 1) (children a) (step cache i a)
                (advance (fuel + 1) q i a) =
              checkPacked EJMGlobalDAGData.nodes step lower dominates gap
                (fuel + 1) (children a) (step cache i a) (advance (fuel + 1) q i a) := by
          rw [show advance (fuel + 1) q i a = append q a by
            simp only [advance, Nat.zero_lt_succ, ↓reduceIte]]
          have hqnext : WellFormed (append q a) :=
            append_wellFormed q a hwell (by omega)
          have hnextinv : (append q a).depth + (fuel + 1) = 21 := by
            dsimp [append]
            omega
          exact ih _ _ _ hqnext hnextinv
        simp only [hchild] <;> exact decide_eq_decide.mpr Iff.rfl

theorem checkFast_eq_original {Cache : Type}
    (step : Cache → Coord → Value → Cache) (lower : Cache → ℤ)
    (fuel : ℕ) (index : Fin EJMGlobalDAGData.Size) (cache : Cache) (q : PackedPartial)
    (hwell : WellFormed q) (hinv : q.depth + fuel = 21) :
    checkFast step lower EJMPartialBoundData.scale fuel index cache q =
      D5.S0.Certificates.FiniteCachedSymmetryDAGReplay.check EJMGlobalDAGData.nodes
        step lower dominates EJMPartialBoundData.scale fuel index cache (decode q) :=
  (checkFast_eq_checkPacked step lower _ fuel index cache q hwell hinv).trans
    (checkPacked_eq_original step lower fuel index cache q hwell hinv)

#print axioms dominatesPacked_eq_original
#print axioms checkFast_eq_original

end D5.S3.Quantum.Entanglement.EJM.EJMCompactDominates
