/- GID: D5/S1/Words/Palindromes/AKMPUniformPrefix
   generality: I
   mirror-B: D5/B/S1/Words/Palindromes/AKMPUniformPrefix
   mirror-E: none(waiver:constructive-word-factorisation)
   anchors: []
   utility: none
   digest: Every proper prefix of either level-k psi image has palindromic length at most k+1. -/

import D5.S1.Words.Palindromes.FridPrefix.PalindromicLength
import Mathlib.Algebra.FreeMonoid.Basic

namespace D5.S1.Words.AKMPUniformPrefix

/-- The substitution from Ambrož, Kadlec, Masáková and Pelantová,
*Palindromic length of words and morphisms in class P*, section 4
(arXiv:1812.00711v2), with `a = true` and `b = false`. -/
def psiLetter : Bool → List Bool
  | true => [true, false, true, false, true]
  | false => [true, false, true]

/-- The free-monoid extension of the letter substitution. -/
def psiEnd : Monoid.End (FreeMonoid Bool) :=
  FreeMonoid.lift (fun c => FreeMonoid.ofList (psiLetter c))

/-- The actual level-`k` substitution image of a single letter. -/
def W (k : ℕ) (c : Bool) : List Bool :=
  FreeMonoid.toList ((psiEnd ^ k) (FreeMonoid.of c))

/-- Uniform proper-prefix bound for both substitution origins. -/
theorem uniform_prefix_pl (k : ℕ) (_hk : 1 ≤ k) (c : Bool) (m : ℕ)
    (hm : m < (W k c).length) : FridPrefix.PL ((W k c).take m) ≤ k + 1 := by
  classical
  have hinv : ∀ n : ℕ, ∀ d : Bool,
      W n d ≠ [] ∧ List.Palindrome (W n d) ∧
      ∀ j : ℕ, j ≤ (W n d).length →
        ∃ ps : List (List Bool), ps.flatten = (W n d).take j ∧
          ps.length ≤ n + 1 ∧ ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p := by
    intro n
    induction n with
    | zero =>
      intro d
      refine ⟨by simp [W], ?_, ?_⟩
      · simpa [W] using List.Palindrome.singleton d
      · intro j hj
        have hj' : j = 0 ∨ j = 1 := by simp [W] at hj; omega
        rcases hj' with rfl | rfl
        · exact ⟨[], by simp, by simp, by simp⟩
        · exact ⟨[[d]], by simp [W], by simp,
            by simpa using And.intro (by simp : [d] ≠ []) (List.Palindrome.singleton d)⟩
    | succ n ih =>
      let A := W n true
      let B := W n false
      let a := A.length
      let b := B.length
      let P := A ++ B ++ A
      let Q := A ++ B ++ A ++ B ++ A
      obtain ⟨hA0, hAp, hAc⟩ := ih true
      obtain ⟨hB0, hBp, hBc⟩ := ih false
      change A ≠ [] at hA0
      change B ≠ [] at hB0
      change ∀ j, j ≤ A.length → ∃ ps : List (List Bool),
        ps.flatten = A.take j ∧ ps.length ≤ n + 1 ∧
        ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p at hAc
      change ∀ j, j ≤ B.length → ∃ ps : List (List Bool),
        ps.flatten = B.take j ∧ ps.length ≤ n + 1 ∧
        ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p at hBc
      have ha : 0 < a := List.length_pos_iff.mpr hA0
      have hb : 0 < b := List.length_pos_iff.mpr hB0
      have hAr : A.reverse = A := hAp.reverse_eq
      have hBr : B.reverse = B := hBp.reverse_eq
      have hP : W (n + 1) false = P := by
        unfold W
        rw [pow_succ]
        change FreeMonoid.toList ((psiEnd ^ n) (psiEnd (FreeMonoid.of false))) = P
        rw [show psiEnd (FreeMonoid.of false) =
          FreeMonoid.of true * FreeMonoid.of false * FreeMonoid.of true from rfl]
        simp only [map_mul, FreeMonoid.toList_mul]
        rfl
      have hQ : W (n + 1) true = Q := by
        unfold W
        rw [pow_succ]
        change FreeMonoid.toList ((psiEnd ^ n) (psiEnd (FreeMonoid.of true))) = Q
        rw [show psiEnd (FreeMonoid.of true) =
          FreeMonoid.of true * FreeMonoid.of false * FreeMonoid.of true *
            FreeMonoid.of false * FreeMonoid.of true from rfl]
        simp only [map_mul, FreeMonoid.toList_mul]
        rfl
      have hP0 : P ≠ [] := by simp [P, List.append_eq_nil_iff, hA0]
      have hQ0 : Q ≠ [] := by simp [Q, List.append_eq_nil_iff, hA0]
      have hPp : List.Palindrome P := List.Palindrome.of_reverse_eq
        (by simp [P, List.reverse_append, hAr, hBr, List.append_assoc])
      have hQp : List.Palindrome Q := List.Palindrome.of_reverse_eq
        (by simp [Q, List.reverse_append, hAr, hBr, List.append_assoc])
      have hQc : ∀ j : ℕ, j ≤ Q.length →
          ∃ ps : List (List Bool), ps.flatten = Q.take j ∧
            ps.length ≤ n + 2 ∧ ∀ p ∈ ps, p ≠ [] ∧ List.Palindrome p := by
        intro j hj
        have hjT : j ≤ 3 * a + 2 * b := by
          simp only [Q, List.length_append] at hj
          dsimp [a, b]
          omega
        by_cases hj1 : j ≤ a
        · obtain ⟨ps, hps, hlen, hp⟩ := hAc j hj1
          refine ⟨ps, ?_, by omega, hp⟩
          rw [show Q = A ++ (B ++ A ++ B ++ A) by simp [Q, List.append_assoc],
            List.take_append_of_le_length hj1]
          exact hps
        · by_cases hj2 : j < a + b
          · obtain ⟨ps, hps, hlen, hp⟩ := hBc (j - a) (by omega)
            refine ⟨A :: ps, ?_, by simpa using Nat.add_le_add_right hlen 1, ?_⟩
            · have hcut : Q.take j = A ++ B.take (j - a) := by
                rw [show Q = A ++ (B ++ (A ++ B ++ A)) by simp [Q, List.append_assoc],
                  List.take_append, List.take_of_length_le (show A.length ≤ j by omega),
                  List.take_append_of_le_length (show j - A.length ≤ B.length by omega)]
              simpa [hps] using hcut.symm
            · intro p hp'
              rcases List.mem_cons.mp hp' with rfl | hp'
              · exact ⟨hA0, hAp⟩
              · exact hp p hp'
          · by_cases hj3 : j ≤ 2 * a + b
            · let r := 2 * a + b - j
              let D := A.drop r
              have hr : r ≤ a := by dsimp [r]; omega
              obtain ⟨ps, hps, hlen, hp⟩ := hAc r hr
              have hcut : Q.take j = A ++ B ++ A.take (a - r) := by
                have he : j - A.length - B.length = a - r := by dsimp [a, b, r] at *; omega
                rw [show Q = A ++ (B ++ (A ++ (B ++ A))) by simp [Q, List.append_assoc],
                  List.take_append, List.take_of_length_le (show A.length ≤ j by omega),
                  List.take_append,
                  List.take_of_length_le (show B.length ≤ j - A.length by omega),
                  List.take_append_of_le_length
                    (show j - A.length - B.length ≤ A.length by omega), he]
                simp [List.append_assoc]
              refine ⟨ps ++ [D ++ B ++ D.reverse], ?_, (by
                  simp only [List.length_append, List.length_singleton]
                  omega), ?_⟩
              · calc
                  (ps ++ [D ++ B ++ D.reverse]).flatten =
                      (A.take r ++ A.drop r) ++ B ++ (A.drop r).reverse := by
                    simp only [List.flatten_append, List.flatten_singleton, hps, D,
                      List.append_assoc]
                  _ = A ++ B ++ A.take (a - r) := by
                    rw [List.take_append_drop, List.reverse_drop, hAr]
                  _ = Q.take j := hcut.symm
              · intro p hp'
                rcases List.mem_append.mp hp' with hp' | hp'
                · exact hp p hp'
                · obtain rfl := List.mem_singleton.mp hp'
                  refine ⟨by simp [List.append_eq_nil_iff, hB0],
                    List.Palindrome.of_reverse_eq ?_⟩
                  simp [List.reverse_append, hBr, List.append_assoc]
            · by_cases hj4 : j < 2 * a + 2 * b
              · obtain ⟨ps, hps, hlen, hp⟩ := hBc (j - (2 * a + b)) (by omega)
                have hPlen : P.length = 2 * a + b := by simp [P, a, b]; omega
                have hcut : Q.take j = P ++ B.take (j - (2 * a + b)) := by
                  rw [show Q = P ++ (B ++ A) by simp [Q, P, List.append_assoc],
                    List.take_append, List.take_of_length_le (show P.length ≤ j by omega),
                    List.take_append_of_le_length (show j - P.length ≤ B.length by omega), hPlen]
                refine ⟨P :: ps, by simpa [hps] using hcut.symm,
                  by simpa using Nat.add_le_add_right hlen 1, ?_⟩
                intro p hp'
                rcases List.mem_cons.mp hp' with rfl | hp'
                · exact ⟨hP0, hPp⟩
                · exact hp p hp'
              · let r := 3 * a + 2 * b - j
                let D := A.drop r
                have hr : r ≤ a := by dsimp [r]; omega
                obtain ⟨ps, hps, hlen, hp⟩ := hAc r hr
                have hcut : Q.take j = A ++ B ++ A ++ B ++ A.take (a - r) := by
                  have he : j - A.length - B.length - A.length - B.length = a - r := by
                    dsimp [a, b, r] at *; omega
                  rw [show Q = A ++ (B ++ (A ++ (B ++ A))) by simp [Q, List.append_assoc],
                    List.take_append, List.take_of_length_le (show A.length ≤ j by omega),
                    List.take_append,
                    List.take_of_length_le (show B.length ≤ j - A.length by omega),
                    List.take_append,
                    List.take_of_length_le
                      (show A.length ≤ j - A.length - B.length by omega),
                    List.take_append,
                    List.take_of_length_le
                      (show B.length ≤ j - A.length - B.length - A.length by omega), he]
                  simp [List.append_assoc]
                refine ⟨ps ++ [D ++ B ++ A ++ B ++ D.reverse], ?_, (by
                    simp only [List.length_append, List.length_singleton]
                    omega), ?_⟩
                · calc
                    (ps ++ [D ++ B ++ A ++ B ++ D.reverse]).flatten =
                        (A.take r ++ A.drop r) ++ B ++ A ++ B ++ (A.drop r).reverse := by
                      simp only [List.flatten_append, List.flatten_singleton, hps, D,
                        List.append_assoc]
                    _ = A ++ B ++ A ++ B ++ A.take (a - r) := by
                      rw [List.take_append_drop, List.reverse_drop, hAr]
                    _ = Q.take j := hcut.symm
                · intro p hp'
                  rcases List.mem_append.mp hp' with hp' | hp'
                  · exact hp p hp'
                  · obtain rfl := List.mem_singleton.mp hp'
                    refine ⟨by simp [List.append_eq_nil_iff, hB0],
                      List.Palindrome.of_reverse_eq ?_⟩
                    simp [List.reverse_append, hAr, hBr, List.append_assoc]
      intro d
      cases d with
      | false =>
        rw [hP]
        refine ⟨hP0, hPp, ?_⟩
        intro j hj
        obtain ⟨ps, hps, hlen, hp⟩ := hQc j (by simp only [Q, P, List.length_append] at *; omega)
        refine ⟨ps, ?_, hlen, hp⟩
        rw [show Q = P ++ (B ++ A) by simp [Q, P, List.append_assoc],
          List.take_append_of_le_length hj] at hps
        exact hps
      | true => simpa [hQ] using And.intro hQ0 (And.intro hQp hQc)
  obtain ⟨ps, hps, hlen, hp⟩ := (hinv k c).2.2 m (Nat.le_of_lt hm)
  exact (Nat.find_le (show FridPrefix.PalFactors ((W k c).take m) ps.length from
    ⟨ps, hps, rfl, hp⟩)).trans hlen

end D5.S1.Words.AKMPUniformPrefix
