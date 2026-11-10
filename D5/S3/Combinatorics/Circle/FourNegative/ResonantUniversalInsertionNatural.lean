/- GID: D5/S3/Combinatorics/Circle/FourNegative/ResonantUniversalInsertionNatural
   generality: I
   mirror-B: none(waiver:universal-resonant-source)
   mirror-E: none(waiver:dependent-physical-source-audit)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Natural target prefixes for the adaptive resonant lift above the boundary. -/
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionSchedule
import D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertionLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion

open SourceWidth PeriodicShortening PeriodicShorteningArithmetic
open RunFirstEarTransport

/-- Every natural prefix of the adaptive lift is legal above the boundary. -/
theorem resonant_target_word_natural_prefix_strict {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell < k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word)
    (n : ℕ) :
    let o := resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
    let targetPrefix := (resonantLiftWord word o).take n
    0 ≤ (targetPrefix.map (resonantTargetFirst k ell w)).sum ∧
      (targetPrefix.map (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell ∧
      0 ≤ (targetPrefix.map (resonantTargetSecond k ell w)).sum ∧
      (targetPrefix.map (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell := by
  dsimp only
  let o := resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
  let block := resonantBlock (k := k) (ell := ell) o
  let f₁ := resonantTargetFirst k ell w
  let f₂ := resonantTargetSecond k ell w
  let H := resonantTargetH k ell
  let N := resonantTargetN k ell
  let targetPrefix := (resonantLiftWord word o).take n
  have inStrip_take {α : Type} (f : α → ℤ) (B h : ℤ)
      (xs : List α) (hs : InStrip f B h xs) (r : ℕ) :
      InStrip f B h (xs.take r) := by
    induction xs generalizing h r with
    | nil => simpa [InStrip] using hs
    | cons x xs ih =>
      cases r with
      | zero => exact ⟨hs.1, hs.2.1⟩
      | succ r =>
        simp only [List.take_succ_cons]
        exact ⟨hs.1, hs.2.1, ih _ hs.2.2 r⟩
  have hblock (i : ℕ) (hi : i < word.length) :
      InStrip f₁ H (resonantFirstState k ell w m (word.take i))
          (block word[i]) ∧
      InStrip f₂ N (resonantSecondState k ell w m (word.take i))
          (block word[i]) := by
    simpa [block, f₁, f₂, H, N, o] using
      (resonant_adaptive_block_strip hw hell hm hdiv hlarge hkl word hsource i hi)
  have aux : ∀ d i, d = word.length - i → i ≤ word.length → ∀ r,
      InStrip f₁ H (resonantFirstState k ell w m (word.take i))
          (((word.drop i).flatMap block).take r) ∧
      InStrip f₂ N (resonantSecondState k ell w m (word.take i))
          (((word.drop i).flatMap block).take r) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i hdi hil r
      by_cases hieq : i = word.length
      · subst i
        have hend := resonant_canonical_complete_prefix hw hell hm hdiv hlarge
          (by omega : ell ≤ k) word hsource word.length
        have hend' :
            0 ≤ resonantFirstState k ell w m word ∧
              resonantFirstState k ell w m word ≤ H ∧
            0 ≤ resonantSecondState k ell w m word ∧
              resonantSecondState k ell w m word ≤ N := by
          simpa [H, N] using hend
        have hbase :
            InStrip f₁ H (resonantFirstState k ell w m word) [] ∧
            InStrip f₂ N (resonantSecondState k ell w m word) [] :=
          ⟨⟨hend'.1, hend'.2.1⟩, ⟨hend'.2.2.1, hend'.2.2.2⟩⟩
        simpa [List.drop_length] using hbase
      · have hi : i < word.length := by omega
        let j := word[i]
        have hdrop : word.drop i = j :: word.drop (i + 1) := by
          simpa [j] using (List.cons_getElem_drop_succ (l := word) (n := i) (h := hi))
        have hb := hblock i hi
        by_cases hr : r ≤ (block j).length
        · have ht : (((word.drop i).flatMap block).take r) = (block j).take r := by
            rw [hdrop]
            simp [List.take_append, hr]
          have htakeF := inStrip_take f₁ H
            (resonantFirstState k ell w m (word.take i)) (block j) hb.1 r
          have htakeS := inStrip_take f₂ N
            (resonantSecondState k ell w m (word.take i)) (block j) hb.2 r
          exact ⟨by simpa [ht] using htakeF, by simpa [ht] using htakeS⟩
        · have hnextF : resonantFirstState k ell w m (word.take (i + 1)) =
              resonantFirstState k ell w m (word.take i) +
                ((block j).map f₁).sum := by
            have ht := List.take_succ_eq_append_getElem hi
            have hs := resonant_state_append hw hell hm hdiv hlarge
              (by omega : ell ≤ k) (word.take i) j
            have hbs := resonant_block_sums hw hell hm hdiv hlarge
              (by omega : ell ≤ k) o j
            rw [ht, hs.1]
            rw [hbs.1]
          have hnextS : resonantSecondState k ell w m (word.take (i + 1)) =
              resonantSecondState k ell w m (word.take i) +
                ((block j).map f₂).sum := by
            have ht := List.take_succ_eq_append_getElem hi
            have hs := resonant_state_append hw hell hm hdiv hlarge
              (by omega : ell ≤ k) (word.take i) j
            have hbs := resonant_block_sums hw hell hm hdiv hlarge
              (by omega : ell ≤ k) o j
            rw [ht, hs.2]
            rw [hbs.2]
          have hdi' : word.length - (i + 1) < d := by omega
          have hrest := ih (word.length - (i + 1)) hdi' (i + 1)
            (by omega) (by omega) (r - (block j).length)
          have hrestF : InStrip f₁ H
              (resonantFirstState k ell w m (word.take i) +
                ((block j).map f₁).sum)
              (((word.drop (i + 1)).flatMap block).take
                (r - (block j).length)) := by
            simpa [hnextF] using hrest.1
          have hrestS : InStrip f₂ N
              (resonantSecondState k ell w m (word.take i) +
                ((block j).map f₂).sum)
              (((word.drop (i + 1)).flatMap block).take
                (r - (block j).length)) := by
            simpa [hnextS] using hrest.2
          have ht : (((word.drop i).flatMap block).take r) =
              block j ++ (((word.drop (i + 1)).flatMap block).take
                (r - (block j).length)) := by
            have hlen_le : (block j).length ≤ r := by omega
            rw [hdrop]
            simp [List.take_append, hlen_le]
          exact ⟨by rw [ht]; exact inStrip_append hb.1 hrestF,
            by rw [ht]; exact inStrip_append hb.2 hrestS⟩
  have hstrip := aux word.length 0 (by simp) (by omega) n
  have hstripF : InStrip f₁ H 0 targetPrefix := by
    change InStrip f₁ H 0 ((List.flatMap block word).take n)
    simpa [block, resonantFirstState] using hstrip.1
  have hstripS : InStrip f₂ N 0 targetPrefix := by
    change InStrip f₂ N 0 ((List.flatMap block word).take n)
    simpa [block, resonantSecondState] using hstrip.2
  have hF := inStrip_prefix hstripF targetPrefix.length
  have hS := inStrip_prefix hstripS targetPrefix.length
  rw [List.take_length] at hF hS
  change 0 ≤ (targetPrefix.map f₁).sum ∧ (targetPrefix.map f₁).sum ≤ H ∧
    0 ≤ (targetPrefix.map f₂).sum ∧ (targetPrefix.map f₂).sum ≤ N
  exact ⟨by simpa only [zero_add] using hF.1,
    by simpa only [zero_add] using hF.2,
    by simpa only [zero_add] using hS.1,
    by simpa only [zero_add] using hS.2⟩

/-/ The adaptive resonant lift is a permutation with zero endpoint charges and
    every natural prefix stays in both target strips. -/
theorem resonant_target_word_of_source_strict {w ell k m : ℕ}
    (hw : 1 ≤ w) (hell : 1 ≤ ell) (hm : m = 2 ^ ell)
    (hdiv : w ∣ m - 1) (hlarge : 3 * w + 1 ≤ m) (hkl : ell < k)
    (word : List (Fin (k + 1))) (hsource : resonantSourceWord k w word) :
    let orientation :=
      resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
    (resonantLiftWord word orientation).Perm (List.finRange (k + ell + 1)) ∧
      ((resonantLiftWord word orientation).map
          (resonantTargetFirst k ell w)).sum = 0 ∧
      ((resonantLiftWord word orientation).map
          (resonantTargetSecond k ell w)).sum = 0 ∧
      ∀ n : ℕ,
        0 ≤ (((resonantLiftWord word orientation).take n).map
              (resonantTargetFirst k ell w)).sum ∧
        (((resonantLiftWord word orientation).take n).map
              (resonantTargetFirst k ell w)).sum ≤ resonantTargetH k ell ∧
        0 ≤ (((resonantLiftWord word orientation).take n).map
              (resonantTargetSecond k ell w)).sum ∧
        (((resonantLiftWord word orientation).take n).map
              (resonantTargetSecond k ell w)).sum ≤ resonantTargetN k ell := by
  dsimp only
  let orientation :=
    resonantAdaptiveOrientation w ell k m (by omega : ell ≤ k) word
  have hend := resonant_target_word_endpoint_of_source hw hell hm hdiv hlarge
    (by omega : ell ≤ k) word hsource orientation
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [orientation] using hend.1
  · simpa [orientation] using hend.2.1
  · simpa [orientation] using hend.2.2
  · intro n
    simpa [orientation] using
      (resonant_target_word_natural_prefix_strict hw hell hm hdiv hlarge hkl
        word hsource n)

end D5.S3.Combinatorics.Circle.FourNegative.ResonantUniversalInsertion
