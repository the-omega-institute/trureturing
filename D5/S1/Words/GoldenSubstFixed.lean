/- GID: D5/S1/Words/GoldenSubstFixed
   generality: I
   mirror-B: D5/B/S1/Words/GoldenSubstFixed
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The infinite golden word is fixed pointwise by Fibonacci substitution. -/

import D5.S1.Words.GoldenBalance

namespace D5.S1.Words

open D5.S0.Tower.GoldenGapWord

/-- The output position at which the substitution image of golden letter `i` starts. -/
def goldenSubstStart (i : Nat) : Nat :=
  i + goldenWindowTrueCount 0 i

/-- Consecutive substitution blocks meet at their computed boundaries. -/
theorem goldenSubstStart_succ (i : Nat) :
    goldenSubstStart (i + 1) =
      goldenSubstStart i + (subst (goldenWord i)).length := by
  classical
  by_cases h : goldenWord i = true <;>
    simp [goldenSubstStart, goldenWindowTrueCount, Finset.range_add_one,
      Finset.filter_insert, subst, h] <;>
    omega

private theorem flatMap_block_decomposition {α β : Type*} (l : List α) (f : α → List β)
    (i : Nat) (hi : i < l.length) (a : α) (hia : l.get ⟨i, hi⟩ = a) :
    l.flatMap f =
      (l.take i).flatMap f ++ (f a ++ (l.drop (i + 1)).flatMap f) := by
  simp only [List.get_eq_getElem] at hia
  calc
    l.flatMap f = ((l.take (i + 1) ++ l.drop (i + 1)).flatMap f) := by
      rw [List.take_append_drop]
    _ = (l.take i).flatMap f ++ (f a ++ (l.drop (i + 1)).flatMap f) := by
      rw [List.flatMap_append, List.take_succ_eq_append_getElem hi,
        List.flatMap_append, List.flatMap_singleton, hia]
      rw [List.append_assoc]

private theorem flatMap_block_index_lt {α β : Type*} (l : List α) (f : α → List β)
    (i : Nat) (hi : i < l.length) (a : α) (hia : l.get ⟨i, hi⟩ = a)
    (j : Fin (f a).length) :
    ((l.take i).flatMap f).length + j.1 < (l.flatMap f).length := by
  rw [flatMap_block_decomposition l f i hi a hia]
  simp only [List.length_append]
  omega

private theorem flatMap_block_get {α β : Type*} (l : List α) (f : α → List β)
    (i : Nat) (hi : i < l.length) (a : α) (hia : l.get ⟨i, hi⟩ = a)
    (j : Fin (f a).length) :
    (l.flatMap f).get
        ⟨((l.take i).flatMap f).length + j.1,
          flatMap_block_index_lt l f i hi a hia j⟩ =
      (f a).get j := by
  let blockPrefix := (l.take i).flatMap f
  have hprefix : blockPrefix ++ f a <+: l.flatMap f := by
    rw [flatMap_block_decomposition l f i hi a hia, ← List.append_assoc]
    exact List.prefix_append _ _
  have hk : blockPrefix.length + j.1 < (blockPrefix ++ f a).length := by
    simp only [List.length_append]
    omega
  have hright :
      blockPrefix.length ≤ blockPrefix.length + j.1 := by
    omega
  have hwithin :
      (blockPrefix ++ f a).get ⟨blockPrefix.length + j.1, hk⟩ = (f a).get j := by
    simp only [List.get_eq_getElem]
    rw [List.getElem_append_right hright]
    simp only [Nat.add_sub_cancel_left]
  exact (hprefix.getElem hk).symm.trans hwithin

private theorem fibWord_take_subst_length (Q i : Nat) (hi : i < (fibWord Q).length) :
    (((fibWord Q).take i).flatMap subst).length = goldenSubstStart i := by
  induction i with
  | zero => simp [goldenSubstStart, goldenWindowTrueCount]
  | succ i ih =>
      have hi' : i < (fibWord Q).length := by omega
      rw [List.take_succ_eq_append_getElem hi', List.flatMap_append,
        List.flatMap_singleton, List.length_append, ih hi']
      have hletter : (fibWord Q)[i] = goldenWord i := by
        simpa only [List.get_eq_getElem] using (goldenWord_eq_fibWord_get Q i hi').symm
      rw [hletter]
      exact (goldenSubstStart_succ i).symm

/-- Every letter in a substituted golden block agrees with the infinite golden word. -/
theorem golden_word_substitution_fixed (i : Nat)
    (j : Fin (subst (goldenWord i)).length) :
    goldenWord (goldenSubstStart i + j.1) = (subst (goldenWord i)).get j := by
  let p := goldenSubstStart i + j.1
  let Q := max i p
  have hiQ : i < (fibWord Q).length := by
    have hdiag := index_lt_diagonal_level Q
    have hle : i ≤ Q := Nat.le_max_left i p
    omega
  have hpQ : p < (fibWord Q).length := by
    have hdiag := index_lt_diagonal_level Q
    have hle : p ≤ Q := Nat.le_max_right i p
    omega
  have hpQ1 : p < (fibWord (Q + 1)).length := by
    have hlength := (fibWord_prefix_succ Q).length_le
    omega
  have hprefix := fibWord_take_subst_length Q i hiQ
  have hblock := flatMap_block_get (fibWord Q) subst i hiQ (goldenWord i)
    (goldenWord_eq_fibWord_get Q i hiQ).symm j
  change goldenWord p = (subst (goldenWord i)).get j
  calc
    goldenWord p = (fibWord (Q + 1)).get ⟨p, hpQ1⟩ :=
      goldenWord_eq_fibWord_get (Q + 1) p hpQ1
    _ = ((fibWord Q).flatMap subst).get ⟨p, by simpa [fibWord] using hpQ1⟩ := rfl
    _ = (subst (goldenWord i)).get j := by
      simpa [p, hprefix] using hblock

private theorem golden_substitution_fixed_small :
    (List.range 13).map goldenSubstStart = [0, 2, 3, 5, 7, 8, 10, 11, 13, 15, 16, 18, 20] ∧
      goldenSubstStart 13 = 21 ∧
      (List.range 13).map goldenWord =
        [true, false, true, true, false, true, false, true, true, false, true, true, false] ∧
      ((List.range 13).map goldenWord).map subst =
        [[true, false], [true], [true, false], [true, false], [true], [true, false],
          [true], [true, false], [true, false], [true], [true, false], [true, false], [true]] ∧
      ((List.range 13).map goldenWord).flatMap subst = (List.range 21).map goldenWord ∧
      (List.range 21).map goldenWord =
        [true, false, true, true, false, true, false, true, true, false, true, true, false,
          true, false, true, true, false, true, false, true] := by
  decide

#print axioms goldenSubstStart_succ
#print axioms golden_word_substitution_fixed

end D5.S1.Words
