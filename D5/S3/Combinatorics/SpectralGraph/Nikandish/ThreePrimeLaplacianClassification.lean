/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/ThreePrimeLaplacianClassification
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/Nikandish/ThreePrimeLaplacianClassification
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Every three-prime ideal-intersection graph has a nonintegral Laplacian spectrum. -/

import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportRepeatedCompletion
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportSmallMinima
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteMinimum3
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteMinimum4
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteMinimum5
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteMinimum6
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportFiniteMinimum7
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointTwoBase
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointTwoTail
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointOneBound
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportEndpointSmallGaps
import D5.S3.Combinatorics.SpectralGraph.Nikandish.SixSupportLargestRoot
import Mathlib.Tactic

/-! The original complete source classification. All finite predicates are
proved by ordinary kernel computation in their supplier modules. The actual
ideal/support/operator bridge carries every noninteger root to a nonzero
eigenvector of the actual graph, including the exact zero-sum condition.
The general higher-prime classification and integer-point certification
questions are separate and are not conclusions of this theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace D5.S3.Combinatorics.SpectralGraph.ThreePrimeLaplacianClassification

open SixSupportClassificationAlgebra
open SixSupportIdealIntersectionLift (exponents)
open IdealIntersectionSupport IdealIntersectionObstructions

private theorem modulus_reindex (p : Fin 3 → ℕ) (k : Fin 3 → ℕ)
    (e : Equiv.Perm (Fin 3)) : modulus (p ∘ e) (k ∘ e) = modulus p k := by
  exact Equiv.prod_comp e (fun i => p i ^ k i)

/-- Every fully distinct ordered triple with minimum at least eight.
Endpoint two is excluded spectrally, without asserting its integer surface empty. -/
theorem distinct_large (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 8 ≤ a)
    (hab : a < b) (hbc : b < c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  intro hint
  have ha0 : 0 < a := by omega
  rcases endpoint_one_or_two p hp hinj a b c ha0 hab.le hbc.le hint with h1 | h2
  · by_cases hb1 : b = a+1
    · subst b
      exact SixSupportEndpointSmallGaps.integer_nonzero a c (by omega) (0 : Fin 2)
        (by simpa using hbc) (by simpa using h1)
    · by_cases hb2 : b = a+2
      · subst b
        exact SixSupportEndpointSmallGaps.integer_nonzero a c (by omega) (1 : Fin 2)
          (by simpa using hbc) (by simpa using h1)
      · have hc := SixSupportEndpointOneBound.third_exponent_bound a b c
          (by omega) hab hbc.le h1
        exact SixSupportLargestRoot.actual_nonintegral p hp hinj a b c
          (by omega) (by omega) hbc.le hc.le hint
  · by_cases ha40 : 40 ≤ a
    · exact SixSupportEndpointTwoTail.actual_nonintegral p hp hinj a b c
        ha40 hab.le hbc.le h2 hint
    · obtain ⟨hbR,hcR⟩ := SixSupportEndpointTwoTail.rectangle a b c
        (by exact_mod_cast ha) (by exact_mod_cast hab.le) (by exact_mod_cast hbc.le) h2
      have hbI : (b : ℤ) < 2*(a : ℤ)-2 := by exact_mod_cast hbR
      have hcI : 4*(c : ℤ) < 9*(a : ℤ)-32 := by
        exact_mod_cast (show 4*(c : ℝ) < 9*(a : ℝ)-32 by linarith)
      exact SixSupportEndpointTwoBase.endpoint_two_nonzero a b c ha (by omega)
        hab (by omega) hbc (by omega) h2

/-- The entire ordered positive exponent domain, including every repetition
and every original small-minimum foundation. -/
theorem sorted (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  have hb : 0 < b := by omega
  have hc : 0 < c := by omega
  by_cases habE : a = b
  · subst b
    exact SixSupportRepeatedCompletion.result p hp hinj a c ha hc
  · by_cases hbcE : b = c
    · subst c
      let e : Equiv.Perm (Fin 3) := Equiv.swap 0 2
      have hk : exponents a b b ∘ e = exponents b b a := by
        funext i; fin_cases i <;> rfl
      have hm := modulus_reindex p (exponents a b b) e
      rw [hk] at hm
      rw [← hm]
      exact SixSupportRepeatedCompletion.result (p ∘ e) (fun i => hp (e i))
        (hinj.comp e.injective) b a hb ha
    · have hab' : a < b := by omega
      have hbc' : b < c := by omega
      by_cases ha1 : a = 1
      · subst a
        exact SixSupportSmallMinima.unit_actual p hp hinj b c hb hc (by omega)
      · by_cases ha2 : a = 2
        · subst a
          exact SixSupportSmallMinima.minimum_two_actual p hp hinj b c hab' hbc'
        · by_cases ha8 : 8 ≤ a
          · exact distinct_large p hp hinj a b c ha8 hab' hbc'
          · by_cases htail : SixSupportFiniteEndpointBase.cutoff a ≤ c
            · exact SixSupportUniformTail.actual_nonintegral p hp hinj a b c
                (by omega) hab hbc htail
            · have hbase : SixSupportFiniteEndpointBase.base a = true := by
                have ha3 : 3 ≤ a := by omega
                have ha7 : a ≤ 7 := by omega
                interval_cases a
                · exact SixSupportFiniteMinimum3.result
                · exact SixSupportFiniteMinimum4.result
                · exact SixSupportFiniteMinimum5.result
                · exact SixSupportFiniteMinimum6.result
                · exact SixSupportFiniteMinimum7.result
              exact SixSupportFiniteEndpointBase.actual_nonintegral p hp hinj a b c ha
                hab' hbc' (by omega) hbase

private theorem reorder (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c A B C : ℕ) (hA : 0 < A)
    (hAB : A ≤ B) (hBC : B ≤ C) (e : Equiv.Perm (Fin 3))
    (hk : exponents a b c ∘ e = exponents A B C) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  have hm := modulus_reindex p (exponents a b c) e
  rw [hk] at hm
  rw [← hm]
  exact sorted (p ∘ e) (fun i => hp (e i)) (hinj.comp e.injective) A B C hA hAB hBC

/-- The received full three-prime classification, on all nonzero proper
ideals of ZMod n and all positive integer exponents, without an ordering premise. -/
theorem result (p : Fin 3 → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ¬ActualLaplacianIntegral (modulus p (exponents a b c)) := by
  by_cases hab : a ≤ b
  · by_cases hbc : b ≤ c
    · exact sorted p hp hinj a b c ha hab hbc
    · by_cases hac : a ≤ c
      · apply reorder p hp hinj a b c a c b ha hac (by omega) (Equiv.swap 1 2)
        funext i; fin_cases i <;> rfl
      · apply reorder p hp hinj a b c c a b hc (by omega) hab
          ((Equiv.swap 0 1).trans (Equiv.swap 1 2))
        funext i; fin_cases i <;> rfl
  · by_cases hac : a ≤ c
    · apply reorder p hp hinj a b c b a c hb (by omega) hac (Equiv.swap 0 1)
      funext i; fin_cases i <;> rfl
    · by_cases hbc : b ≤ c
      · apply reorder p hp hinj a b c b c a hb hbc (by omega)
          ((Equiv.swap 1 2).trans (Equiv.swap 0 1))
        funext i; fin_cases i <;> rfl
      · apply reorder p hp hinj a b c c b a hc (by omega) (by omega) (Equiv.swap 0 2)
        funext i; fin_cases i <;> rfl

#print axioms distinct_large
#print axioms sorted
#print axioms result
end D5.S3.Combinatorics.SpectralGraph.ThreePrimeLaplacianClassification
