/- GID: D5/S3/Arith/Lattices/PrimeCyclotomicTraceImage
   generality: G
   mirror-B: D5/B/S3/Arith/Lattices/PrimeCyclotomicTraceImage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: The prime-cyclotomic trace Gram template has an exact integral-image criterion with an explicit unique preimage. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage

open scoped BigOperators

/-- The integral trace Gram template of size `n+1`, with the first coordinate
separated. For the real prime-cyclotomic field, `p = 2*n+3` and `d = n+1`.
The algebraic definition also makes sense when `2*n+3` is not prime. -/
def traceGram (n : ℕ) (x : ℤ × (Fin n → ℤ)) : ℤ × (Fin n → ℤ) :=
  (((n : ℤ) + 1) * x.1 - ∑ i, x.2 i,
    fun i => (2 * (n : ℤ) + 3) * x.2 i - x.1 - 2 * ∑ j, x.2 j)

/-- A completely specified integer candidate for the preimage. Its correctness
is certified by the divisibility conditions in `integral_image`; integer division
is part of the construction, not an assumption of rational invertibility. -/
def reconstruct (n : ℕ) (y : ℤ × (Fin n → ℤ)) : ℤ × (Fin n → ℤ) :=
  let z : Fin n → ℤ := fun i => (y.2 i - 2 * y.1) / (2 * (n : ℤ) + 3)
  (y.1 + ∑ i, z i, fun i => y.1 + (∑ j, z j) + z i)

/-- The integral image consists exactly of the vectors with
`y_i = 2*y_0` modulo `2*n+3`. On this domain the displayed reconstruction is
correct and is the unique preimage. No inverse, determinant, trace-dual basis,
or Smith normal form is assumed. The empty lower block `n=0` is included. -/
theorem integral_image (n : ℕ) (y : ℤ × (Fin n → ℤ)) :
    (∀ i, (2 * (n : ℤ) + 3) ∣ y.2 i - 2 * y.1) ↔
      traceGram n (reconstruct n y) = y ∧
        ∀ x, traceGram n x = y → x = reconstruct n y := by
  let p : ℤ := 2 * (n : ℤ) + 3
  have hp : 0 < p := by dsimp [p]; omega
  have hdifference (x : ℤ × (Fin n → ℤ)) (i : Fin n) :
      (traceGram n x).2 i - 2 * (traceGram n x).1 =
        p * (x.2 i - x.1) := by
    dsimp [traceGram, p]
    ring
  constructor
  · intro hy
    let z : Fin n → ℤ := fun i => (y.2 i - 2 * y.1) / p
    have hz (i : Fin n) : p * z i = y.2 i - 2 * y.1 :=
      Int.mul_ediv_cancel' (hy i)
    have hsum :
        (∑ i : Fin n, y.1 + (∑ j, z j) + z i) =
          (n : ℤ) * (y.1 + ∑ j, z j) + ∑ i, z i := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hright : traceGram n (reconstruct n y) = y := by
      apply Prod.ext
      · change ((n : ℤ) + 1) * (y.1 + ∑ j, z j) -
          (∑ i : Fin n, y.1 + (∑ j, z j) + z i) = y.1
        rw [hsum]
        ring
      · funext i
        change p * (y.1 + (∑ j, z j) + z i) - (y.1 + ∑ j, z j) -
          2 * (∑ i : Fin n, y.1 + (∑ j, z j) + z i) = y.2 i
        rw [hsum]
        have hzi := hz i
        dsimp [p] at hzi ⊢
        nlinarith
    refine ⟨hright, ?_⟩
    intro x hx
    have hcoords (i : Fin n) : x.2 i - x.1 = z i := by
      apply mul_left_cancel₀ (ne_of_gt hp)
      have hdi := hdifference x i
      rw [hx] at hdi
      exact hdi.symm.trans (hz i).symm
    have hsumx : (∑ i, x.2 i) = (n : ℤ) * x.1 + ∑ i, z i := by
      calc
        (∑ i, x.2 i) = ∑ i : Fin n, x.1 + z i := by
          apply Finset.sum_congr rfl
          intro i _
          have hi := hcoords i
          omega
        _ = (n : ℤ) * x.1 + ∑ i, z i := by
          simp [Finset.sum_add_distrib, nsmul_eq_mul]
    have hx0 : x.1 = y.1 + ∑ i, z i := by
      have hfirst := congrArg Prod.fst hx
      change ((n : ℤ) + 1) * x.1 - (∑ i, x.2 i) = y.1 at hfirst
      rw [hsumx] at hfirst
      nlinarith
    apply Prod.ext
    · exact hx0
    · funext i
      change x.2 i = y.1 + (∑ j, z j) + z i
      have hi := hcoords i
      omega
  · rintro ⟨hy, _⟩ i
    refine ⟨(reconstruct n y).2 i - (reconstruct n y).1, ?_⟩
    have hdi := hdifference (reconstruct n y) i
    simpa only [hy] using hdi

#print axioms integral_image

end D5.S3.Arith.Lattices.PrimeCyclotomicTraceImage
