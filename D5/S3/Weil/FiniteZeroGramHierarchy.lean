/- GID: D5/S3/Weil/FiniteZeroGramHierarchy
   generality: I
   mirror-B: D5/B/S3/Weil/FiniteZeroGramHierarchy
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A finite weighted zero-resolvent Gram matrix has an exact
     nonnegative determinant-square contribution. -/

import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Tactic

/-!
# Finite zero Gram hierarchy

Library-search and duplication audit trail (2026-09-03):
* Literal and spelling-variant searches for finite zero Gram, resolvent, Pick,
  determinant-square, `PosSemidef`, and `det_conjTranspose` found nearby
  oscillator and weighted-readout Gram results, but no owner of this weighted
  resolvent determinant formula.
* The formalization-receipt and digest indices contain no receipt for the source
  atom. The generic `gram` hit was inspected and is not equivalent.
* Generalized-body searches found Mathlib's positive-semidefinite congruence and
  determinant lemmas, but no rectangular Cauchy--Binet theorem in the pinned
  library. The in-flight lane scan likewise found no equivalent declaration.
* The source's infinite subset sum needs enumeration and convergence hypotheses
  that it does not state. This finite equal-cardinality theorem is exactly one
  nonnegative subset contribution. Its claimed converse to RH is omitted:
  positivity follows from the Gram construction for every real ordinate family,
  so it cannot by itself force the ordinates to arise from critical-line zeros.
-/

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ComplexOrder Matrix

namespace D5.S3.Weil.FiniteZeroGramHierarchy

/-- Resolvent coordinates of a finite real ordinate family at complex sampling
nodes. The theorem below rules out the totalized-inverse zero-denominator case
when the nodes lie in the open upper half-plane. -/
def zeroResolventMatrix {ι : Type*} (nodes : ι → ℂ) (ordinates : ι → ℝ) :
    Matrix ι ι ℂ :=
  fun a k => ((ordinates k : ℂ) - nodes a)⁻¹

/-- The finite weighted zero kernel, written as a diagonal congruence. -/
def finiteZeroGramMatrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (ordinates weights : ι → ℝ) : Matrix ι ι ℂ :=
  zeroResolventMatrix nodes ordinates *
    Matrix.diagonal (fun k => (weights k : ℂ)) *
      (zeroResolventMatrix nodes ordinates)ᴴ

/-- For equally many sampling nodes and selected real ordinates, nonnegative
weights give a positive-semidefinite resolvent Gram matrix. Its determinant is
the selected-family contribution: the product of the weights times the squared
modulus of the Cauchy resolvent determinant. -/
theorem finite_zero_gram_hierarchy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℂ) (ordinates weights : ι → ℝ)
    (hnodes : ∀ a, 0 < (nodes a).im)
    (hweights : ∀ k, 0 ≤ weights k) :
    (∀ a k, (ordinates k : ℂ) - nodes a ≠ 0) ∧
      (∀ a b, finiteZeroGramMatrix nodes ordinates weights a b =
        ∑ k, zeroResolventMatrix nodes ordinates a k * (weights k : ℂ) *
          star (zeroResolventMatrix nodes ordinates b k)) ∧
      (finiteZeroGramMatrix nodes ordinates weights).PosSemidef ∧
      Matrix.det (finiteZeroGramMatrix nodes ordinates weights) =
        (∏ k, (weights k : ℂ)) * Matrix.det (zeroResolventMatrix nodes ordinates) *
          star (Matrix.det (zeroResolventMatrix nodes ordinates)) ∧
      0 ≤ Matrix.det (finiteZeroGramMatrix nodes ordinates weights) := by
  have hdenominator : ∀ a k, (ordinates k : ℂ) - nodes a ≠ 0 := by
    intro a k hzero
    have heq : (ordinates k : ℂ) = nodes a := sub_eq_zero.mp hzero
    have him := congrArg Complex.im heq
    simp only [Complex.ofReal_im] at him
    exact (ne_of_gt (hnodes a)) him.symm
  have hentries : ∀ a b, finiteZeroGramMatrix nodes ordinates weights a b =
      ∑ k, zeroResolventMatrix nodes ordinates a k * (weights k : ℂ) *
        star (zeroResolventMatrix nodes ordinates b k) := by
    intro a b
    simp [finiteZeroGramMatrix, Matrix.mul_apply, Matrix.diagonal_apply]
  have hdiagonal :
      (Matrix.diagonal (fun k => (weights k : ℂ)) : Matrix ι ι ℂ).PosSemidef := by
    refine Matrix.PosSemidef.diagonal ?_
    intro k
    exact RCLike.ofReal_nonneg.mpr (hweights k)
  have hpositive : (finiteZeroGramMatrix nodes ordinates weights).PosSemidef := by
    exact hdiagonal.mul_mul_conjTranspose_same (zeroResolventMatrix nodes ordinates)
  have hdeterminant :
      Matrix.det (finiteZeroGramMatrix nodes ordinates weights) =
        (∏ k, (weights k : ℂ)) * Matrix.det (zeroResolventMatrix nodes ordinates) *
          star (Matrix.det (zeroResolventMatrix nodes ordinates)) := by
    simp only [finiteZeroGramMatrix, Matrix.det_mul, Matrix.det_diagonal,
      Matrix.det_conjTranspose]
    ring
  exact ⟨hdenominator, hentries, hpositive, hdeterminant, hpositive.det_nonneg⟩

/-- The determinant lower bound is sharp even with two distinct ordinates and
strictly positive weights: repeated upper-half-plane sampling nodes give two
identical resolvent rows. -/
theorem finite_zero_gram_lower_bound_sharp :
    ∃ (nodes : Fin 2 → ℂ) (ordinates weights : Fin 2 → ℝ),
      (∀ a, 0 < (nodes a).im) ∧ Function.Injective ordinates ∧
      (∀ k, 0 < weights k) ∧
      Matrix.det (finiteZeroGramMatrix nodes ordinates weights) = 0 := by
  let nodes : Fin 2 → ℂ := fun _ => Complex.I
  let ordinates : Fin 2 → ℝ := ![0, 1]
  let weights : Fin 2 → ℝ := fun _ => 1
  refine ⟨nodes, ordinates, weights, ?_, ?_, ?_, ?_⟩
  · intro a
    simp [nodes]
  · intro a b hab
    fin_cases a <;> fin_cases b <;> simp [ordinates] at hab ⊢
  · intro k
    simp [weights]
  · have hdeterminant :=
      (finite_zero_gram_hierarchy nodes ordinates weights
        (by intro a; simp [nodes]) (by intro k; simp [weights])).2.2.2.1
    rw [hdeterminant]
    have hresolvent : Matrix.det (zeroResolventMatrix nodes ordinates) = 0 := by
      simp [zeroResolventMatrix, nodes, ordinates, Matrix.det_fin_two]
      ring
    simp [hresolvent]

#print axioms finite_zero_gram_hierarchy
#print axioms finite_zero_gram_lower_bound_sharp

end D5.S3.Weil.FiniteZeroGramHierarchy
