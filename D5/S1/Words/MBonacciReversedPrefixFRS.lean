/- GID: D5/S1/Words/MBonacciReversedPrefixFRS
   generality: G
   mirror-B: D5/B/S1/Words/MBonacciReversedPrefixFRS
   mirror-E: none(waiver:pure-word-combinatorics)
   anchors: []
   utility: none
   digest: Reversed prefixes of the actual m-bonacci word are fully right-special. -/

import D5.S1.Words.MBonacciSentinelDesubstitution
import Mathlib.Data.List.Infix
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.MBonacciReversedPrefixFRS

open D5.S1.Words.MBonacciSentinelDesubstitution
open RankOneMorphismIterationBound (subst image)
open AbelianBorders.AbelianBorderQuestionDefs (factor)

variable {m : ℕ} (hm : 2 ≤ m)

private def predecessor (a : Fin m) : Fin m :=
  if h : a.val = 0 then
    ⟨m - 1, Nat.sub_lt (by omega) (by omega)⟩
  else
    ⟨a.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) a.isLt⟩

private lemma predecessor_rot (a : Fin m) :
    rot hm (predecessor hm a) = a := by
  by_cases hzero : a.val = 0
  · simp only [predecessor, dif_pos hzero]
    unfold rot
    split_ifs with h
    · exfalso
      change m - 1 + 1 < m at h
      omega
    · apply Fin.ext
      exact hzero.symm
  · have ha1 : 0 < a.val := by omega
    simp only [predecessor, dif_neg hzero]
    unfold rot
    by_cases hpred : a.val - 1 + 1 < m
    · simp only [dif_pos hpred]
      apply Fin.ext
      simp
      omega
    · exfalso
      change ¬ (a.val - 1 + 1 < m) at hpred
      have ha := a.isLt
      omega

private def letterStart : ℕ → ℕ
  | 0 => 0
  | k + 1 => boundary hm (letterStart k) + 1

private def cyclicLetter (k : ℕ) : Fin m :=
  ⟨k % m, Nat.mod_lt _ (by omega)⟩

private lemma cyclicLetter_rot (k : ℕ) :
    rot hm (cyclicLetter hm k) = cyclicLetter hm (k + 1) := by
  apply Fin.ext
  have hrot := (actual_word_laws hm).2.2.2.2.2.2 (cyclicLetter hm k)
  simpa [cyclicLetter, Nat.add_mod] using hrot

private lemma letterStart_value (k : ℕ) :
    word hm (letterStart hm k) = cyclicLetter hm k := by
  induction k with
  | zero =>
      simp [letterStart, word, image, phi, zero, cyclicLetter, show 1 < m by omega]
  | succ k ih =>
      let i := letterStart hm k
      have hnext : word hm (boundary hm i + 1) = rot hm (word hm i) := by
        by_cases h : (word hm i).val + 1 < m
        · have hb := (actual_word_laws hm).2.2.2.2.1 i
          have hh := congrArg (fun s : List (Fin m) => s[1]?) hb
          simpa [factor, phi, rot, h] using hh
        · have hs := (actual_word_laws hm).2.2.2.1
          have heq : boundary hm i + 1 = boundary hm (i + 1) := by
            rw [hs (i + 1), Finset.sum_range_succ, ← hs i]
            simp [phi, h]
          rw [heq]
          have hb := (actual_word_laws hm).2.2.2.2.1 (i + 1)
          have hh := congrArg (fun s : List (Fin m) => s[0]?) hb
          have hlen : 0 < (phi hm (word hm (i + 1))).length := by
            unfold phi
            split_ifs <;> simp
          have hfirst : (phi hm (word hm (i + 1)))[0]? = some (zero hm) := by
            unfold phi
            split_ifs <;> simp
          rw [hfirst] at hh
          simpa [factor, hlen, rot, h] using hh
      rw [letterStart]
      calc
        word hm (boundary hm (letterStart hm k) + 1) =
            rot hm (word hm (letterStart hm k)) := hnext
        _ = rot hm (cyclicLetter hm k) := by rw [ih]
        _ = cyclicLetter hm (k + 1) := cyclicLetter_rot hm k

private lemma singleton_occurrence (a : Fin m) :
    ∃ q : ℕ, Occ hm [a] q := by
  refine ⟨letterStart hm a.val, ?_⟩
  have h := letterStart_value hm a.val
  have ha : cyclicLetter hm a.val = a := by
    apply Fin.ext
    simp [cyclicLetter, Nat.mod_eq_of_lt a.isLt]
  rw [ha] at h
  simpa [Occ, factor] using h

def sentinelIter : ℕ → List (Fin m)
  | 0 => []
  | t + 1 => T hm (sentinelIter t)

private lemma sentinel_occurrence (t : ℕ) :
    Occ hm (sentinelIter hm t) 0 := by
  induction t with
  | zero =>
      simp [sentinelIter, Occ, factor]
  | succ t iht =>
      have h := (occurrence_transport hm (sentinelIter hm t) 0 iht).2.1
      have hzero := (actual_word_laws hm).2.2.1
      simpa [sentinelIter, hzero] using h

lemma sentinel_frs (t : ℕ) :
    FRS hm (sentinelIter hm t) := by
  induction t with
  | zero =>
      intro a
      exact singleton_occurrence hm a
  | succ t iht =>
      intro a
      let b := predecessor hm a
      obtain ⟨q, hq⟩ := iht b
      have h := (right_extension_occurrence_iff hm (sentinelIter hm t) b (boundary hm q)).2
        ⟨q, rfl, hq⟩
      exact ⟨boundary hm q, by simpa [sentinelIter, b, predecessor_rot] using h⟩

private lemma sentinel_succ_length (t : ℕ) :
    (sentinelIter hm (t + 1)).length =
      boundary hm (sentinelIter hm t).length + 1 := by
  have h := sentinel_occurrence hm t
  unfold Occ at h
  simp [sentinelIter, T, boundary, h]

private lemma sentinel_length_bound (t : ℕ) :
    t ≤ (sentinelIter hm t).length := by
  induction t with
  | zero => simp [sentinelIter]
  | succ t iht =>
      have hstrict := (actual_word_laws hm).2.1
      have hle : (sentinelIter hm t).length ≤
          boundary hm (sentinelIter hm t).length :=
        hstrict.le_apply
      have hlen := sentinel_succ_length hm t
      omega

private lemma zero_reverse_phi (a : Fin m) :
    [zero hm] ++ (phi hm a).reverse = phi hm a ++ [zero hm] := by
  unfold phi
  split_ifs <;> simp

private lemma sentinel_reverse (s : List (Fin m)) :
    (T hm s).reverse = T hm s.reverse := by
  induction s with
  | nil =>
      simp [T, subst]
  | cons a s ih =>
      have hi : [zero hm] ++ (subst (phi hm) s).reverse =
          subst (phi hm) s.reverse ++ [zero hm] := by
        simpa [T] using ih
      calc
        (T hm (a :: s)).reverse =
            [zero hm] ++ (subst (phi hm) s).reverse ++ (phi hm a).reverse := by
              simp [T, subst, List.reverse_append, List.append_assoc]
        _ = (subst (phi hm) s.reverse ++ [zero hm]) ++
              (phi hm a).reverse := by rw [hi]
        _ = subst (phi hm) s.reverse ++ (phi hm a) ++ [zero hm] := by
              simpa [List.append_assoc] using
                congrArg (List.append (subst (phi hm) s.reverse))
                  (zero_reverse_phi hm a)
        _ = T hm (a :: s).reverse := by simp [T, subst, List.append_assoc]

private lemma sentinel_palindrome (t : ℕ) :
    (sentinelIter hm t).reverse = sentinelIter hm t := by
  induction t with
  | zero => simp [sentinelIter]
  | succ t iht =>
      simp [sentinelIter, sentinel_reverse hm, iht]

private lemma factor_drop_occurrence {s : List (Fin m)} {q d : ℕ}
    (h : Occ hm s q) :
    Occ hm (s.drop d) (q + d) := by
  unfold Occ at h ⊢
  rw [List.length_drop]
  have hmap := congrArg (List.drop d) h
  unfold factor at hmap
  rw [← List.map_drop, List.range_eq_range', List.drop_range'] at hmap
  simp only [Nat.mul_one, Nat.zero_add] at hmap
  rw [List.range'_eq_map_range, List.map_map] at hmap
  simpa [factor, Function.comp_def, Nat.add_assoc] using hmap



private lemma prefix_take (ell t : ℕ) (h : ell ≤ (sentinelIter hm t).length) :
    (sentinelIter hm t).take ell = factor (word hm) 0 ell := by
  have hp := sentinel_occurrence hm t
  unfold Occ at hp
  have hh := congrArg (List.take ell) hp
  rw [factor, ← List.map_take, List.take_range, Nat.min_eq_left h] at hh
  exact hh.symm


/-- Every reversed prefix of the actual m-bonacci word is an actual fully right-special factor. -/
theorem reversed_prefix_fully_right_special (ell : ℕ) :
    let r := (factor (word hm) 0 ell).reverse
    r.length = ell ∧ (∃ q : ℕ, Occ hm r q) ∧ FRS hm r := by
  let p := sentinelIter hm ell
  have hbound : ell ≤ p.length := by
    exact sentinel_length_bound hm ell
  have htake : p.take ell = factor (word hm) 0 ell := by
    exact prefix_take hm ell ell hbound
  have hpalm : p.reverse = p := by
    exact sentinel_palindrome hm ell
  let d := p.length - ell
  have hr : (factor (word hm) 0 ell).reverse = p.drop d := by
    rw [← htake, List.reverse_take, hpalm]
  have hlen : (factor (word hm) 0 ell).reverse.length = ell := by
    simp [factor]
  refine ⟨hlen, ?_, ?_⟩
  · have hp := sentinel_occurrence hm ell
    have hd := factor_drop_occurrence (hm := hm) (s := p) (q := 0) (d := d) hp

    exact ⟨d, by simpa [p, d, hr] using hd⟩
  · intro a
    obtain ⟨q, hq⟩ := sentinel_frs hm ell a
    have hh := factor_drop_occurrence (hm := hm) (d := d) hq
    have hdrop : (p ++ [a]).drop d = p.drop d ++ [a] :=
      List.drop_append_of_le_length (Nat.sub_le _ _)
    rw [hdrop, ← hr] at hh
    exact ⟨q + d, hh⟩

end D5.S1.Words.MBonacciReversedPrefixFRS
