/- GID: D5/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients
   generality: I
   mirror-B: D5/B/S1/Words/Complexity/PositivePairs/Coefficients/MagnusWordCoefficients
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual Magnus coefficients equal scattered-subword multiplicities. -/

import D5.S1.Words.Complexity.PositivePairs.Coefficients.CutoffCoefficientAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients

open D5.S1.Words.Complexity.LyndonBrackets.LyndonBracketAlgebra
open D5.S1.Words.Complexity.VivionBinomialConverseFails

variable {A : Type*}

/-- The actual Magnus polynomial `M(w) = ∏ (1 + X_a)`, in source order. -/
noncomputable def magnusPolynomial : List A → WordPolynomial A
  | [] => 1
  | a :: source =>
      (1 + wordMonomial [a]) * magnusPolynomial source

/-- The actual Magnus polynomial sends word concatenation to multiplication. -/
theorem magnusPolynomial_append (left right : List A) :
    magnusPolynomial (left ++ right) =
      magnusPolynomial left * magnusPolynomial right := by
  induction left with
  | nil => simp [magnusPolynomial]
  | cons a left ih =>
      simp only [List.cons_append, magnusPolynomial, ih, mul_assoc]

/-- The coefficient of a word in the actual Magnus polynomial is its frozen
scattered-subword count. -/
theorem magnusPolynomial_coeff_scatteredCount [DecidableEq A]
    (source pattern : List A) :
    (magnusPolynomial source).coeff (FreeMonoid.ofList pattern) =
      (scatteredCount pattern source : ℤ) := by
  classical
  have generator_mul_coeff (a : A) (p : WordPolynomial A) (pattern : List A) :
      (wordMonomial [a] * p).coeff (FreeMonoid.ofList pattern) =
        match pattern with
        | [] => 0
        | b :: tail => if b = a then p.coeff (FreeMonoid.ofList tail) else 0 := by
    cases pattern with
    | nil =>
        simp [wordMonomial, MonoidAlgebra.coeff_mul]
    | cons b tail =>
        by_cases h : b = a
        · subst b
          simp [wordMonomial]
        · simp only [if_neg h]
          rw [← Finsupp.notMem_support_iff]
          intro hmem
          have hproduct := MonoidAlgebra.support_coeff_mul_subset
            (wordMonomial [a]) p hmem
          rcases Finset.mem_mul.mp hproduct with ⟨left, hleft, right, _, heq⟩
          simp only [wordMonomial, MonoidAlgebra.coeff_single,
            Finsupp.support_single _ one_ne_zero,
            Finset.mem_singleton] at hleft
          subst left
          have lists := congrArg FreeMonoid.toList heq
          simp only [FreeMonoid.toList_mul, FreeMonoid.toList_ofList,
            List.singleton_append, List.cons.injEq] at lists
          exact h lists.1.symm
  induction source generalizing pattern with
  | nil =>
      cases pattern <;>
        simp [magnusPolynomial, scatteredCount, MonoidAlgebra.one_def]
  | cons a source ih =>
      rw [magnusPolynomial]
      simp only [add_mul, one_mul, MonoidAlgebra.coeff_add,
        Finsupp.add_apply, generator_mul_coeff]
      cases pattern with
      | nil => simpa [scatteredCount] using ih []
      | cons b tail =>
          change
            (magnusPolynomial source).coeff (FreeMonoid.ofList (b :: tail)) +
                (if b = a then
                  (magnusPolynomial source).coeff (FreeMonoid.ofList tail)
                else 0) =
              (scatteredCount (b :: tail) (a :: source) : ℤ)
          rw [ih (b :: tail)]
          by_cases h : b = a
          · subst b
            rw [ih tail]
            simp [scatteredCount]
          · simp [scatteredCount, h]

/-- The degree-one part of a word is its abelianized letter sum. -/
noncomputable def wordAbelianization : List A → WordPolynomial A
  | [] => 0
  | a :: source => wordMonomial [a] + wordAbelianization source

theorem wordAbelianization_append (left right : List A) :
    wordAbelianization (left ++ right) =
      wordAbelianization left + wordAbelianization right := by
  induction left with
  | nil => simp [wordAbelianization]
  | cons a left ih => simp [wordAbelianization, ih, add_assoc]

theorem wordAbelianization_coeff_singleton [DecidableEq A]
    (source : List A) (b : A) :
    (wordAbelianization source).coeff (FreeMonoid.ofList [b]) =
      (scatteredCount [b] source : ℤ) := by
  induction source with
  | nil => simp [wordAbelianization, scatteredCount]
  | cons a source ih =>
      rw [wordAbelianization, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]
      by_cases h : b = a
      · subst b
        simp [wordMonomial, scatteredCount, add_comm]
      · have hab : (FreeMonoid.of a : FreeMonoid A) ≠ FreeMonoid.of b := by
          intro hab
          have lists := congrArg FreeMonoid.toList hab
          exact h (by simpa using lists.symm)
        simp [wordMonomial, scatteredCount, h, hab]

theorem wordAbelianization_coeff_empty (source : List A) :
    (wordAbelianization source).coeff 1 = 0 := by
  induction source with
  | nil => simp [wordAbelianization]
  | cons a source ih =>
      have hne : (FreeMonoid.of a : FreeMonoid A) ≠ 1 := by
        intro h
        have lists := congrArg FreeMonoid.toList h
        simp at lists
      simp [wordAbelianization, wordMonomial, hne, ih]


end D5.S1.Words.Complexity.PositivePairs.Coefficients.MagnusWordCoefficients
