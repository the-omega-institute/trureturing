/- GID: D5/S1/Words/Powers/CommutingWords
   generality: G
   mirror-B: D5/B/S1/Words/Powers/CommutingWords
   mirror-E: none(waiver:abstract-word-classification-without-separate-evidence-artifact)
   anchors: []
   utility: none
   digest: Two finite words commute exactly when they are natural powers of a common word. -/

import D5.S1.Words.Powers.WordPower
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.Group.Commute.Defs

/-!
Commuting finite words are powers of a common word. The common word is obtained
by descent on the sum of the lengths, removing a shorter prefix at each step.
The alphabet is arbitrary, and empty words and zero exponents are included.
-/

namespace D5.S1.Words.Powers.CommutingWords

universe u

private theorem ofList_wordPower {α : Type u} (m : Nat) (w : List α) :
    FreeMonoid.ofList (wordPower m w) = FreeMonoid.ofList w ^ m := by
  simp only [wordPower, FreeMonoid.ofList_flatten, List.map_replicate,
    List.prod_replicate]

private theorem wordPower_append {α : Type u} (m n : Nat) (w : List α) :
    wordPower m w ++ wordPower n w = wordPower (m + n) w := by
  apply FreeMonoid.ofList.injective
  simp only [FreeMonoid.ofList_append, ofList_wordPower, pow_add]

/-- Two finite words commute if and only if they are natural powers of a common
word. No finiteness or decidable equality assumption on the alphabet is needed. -/
theorem commute_iff_common_power {α : Type u} (u v : List α) :
    u ++ v = v ++ u ↔
      ∃ w : List α, ∃ m n : Nat, u = wordPower m w ∧ v = wordPower n w := by
  constructor
  · intro huv
    have extract : ∀ N : Nat, ∀ a b : List α,
        a.length + b.length = N → a ++ b = b ++ a →
          ∃ w : List α, ∃ m n : Nat,
            a = wordPower m w ∧ b = wordPower n w := by
      intro N
      induction N using Nat.strongRecOn with
      | ind N ih =>
          intro a b hN hab
          cases a with
          | nil => exact ⟨b, 0, 1, by simp, by simp⟩
          | cons x xs =>
              cases b with
              | nil => exact ⟨x :: xs, 1, 0, by simp, by simp⟩
              | cons y ys =>
                  rcases List.append_eq_append_iff.mp hab with
                    ⟨r, hb, hb'⟩ | ⟨r, ha, ha'⟩
                  · have hlen : (y :: ys).length = (x :: xs).length + r.length := by
                      rw [hb, List.length_append]
                    have hsmall : (x :: xs).length + r.length < N := by
                      simp only [List.length_cons] at hN hlen ⊢
                      omega
                    obtain ⟨w, m, n, hm, hn⟩ :=
                      ih ((x :: xs).length + r.length) hsmall (x :: xs) r rfl
                        (hb.symm.trans hb')
                    refine ⟨w, m, m + n, hm, ?_⟩
                    rw [hb, hm, hn, wordPower_append]
                  · have hlen : (x :: xs).length = (y :: ys).length + r.length := by
                      rw [ha, List.length_append]
                    have hsmall : (y :: ys).length + r.length < N := by
                      simp only [List.length_cons] at hN hlen ⊢
                      omega
                    obtain ⟨w, m, n, hm, hn⟩ :=
                      ih ((y :: ys).length + r.length) hsmall (y :: ys) r rfl
                        (ha.symm.trans ha')
                    refine ⟨w, m + n, m, ?_, hm⟩
                    rw [ha, hm, hn, wordPower_append]
    exact extract (u.length + v.length) u v rfl huv
  · rintro ⟨w, m, n, rfl, rfl⟩
    apply FreeMonoid.ofList.injective
    simpa only [FreeMonoid.ofList_append, ofList_wordPower] using
      (Commute.pow_pow_self (FreeMonoid.ofList w) m n).eq

end D5.S1.Words.Powers.CommutingWords
