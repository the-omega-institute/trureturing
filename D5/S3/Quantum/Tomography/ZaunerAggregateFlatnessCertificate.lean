/- GID: D5/S3/Quantum/Tomography/ZaunerAggregateFlatnessCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ZaunerAggregateFlatnessCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Canonical order-six Zauner transitions have twenty-four structural zeros; row-Gram mass conservation sharpens their scaled three-frame-potential margin from twenty-four to seventy-two. -/

import D5.S3.Quantum.Tomography.SupportFaceFlatnessDefect

/- Library-search audit trail (2026-09-04):
   * Reuses the correct fixed-edge structural-zero theorem, the normalized
     scalar defect, the scaled-relative-Gram three-frame potential, and the
     support-face row-mass theorem.
   * Reuses `Fintype.sum_prod_type`, `Fin.sum_univ_two`, and
     `Fin.sum_univ_three` to enumerate the exact order-six carrier. No new
     zero-count, matrix carrier, or flatness objective is introduced.
-/

open scoped BigOperators Matrix

noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Quantum.Tomography.ZaunerAggregateFlatnessCertificate

open Matrix
open D5.S3.Quantum.Tomography.MUBHadamardCompatibility
open D5.S3.Quantum.Tomography.ZaunerCompletionFibre
open D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential
open D5.S3.Quantum.Tomography.SupportFaceFlatnessDefect

/-- All twenty-four entries connecting distinct three-cycle modes vanish in
the normalized canonical transition. Summing their exact `1/36` contributions
gives the aggregate flatness-defect margin `2/3`. -/
theorem zaunerCanonicalCompletion_normalized_defect_ge_two_thirds
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    (2 / 3 : ℝ) ≤
      ∑ p, ∑ q,
        (Complex.normSq
          ((((2 : ℂ)⁻¹) •
            (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)) p q) -
          (1 / 6 : ℝ)) ^ 2 := by
  let A : ComplexSquare (Fin 2 × Fin 3) :=
    ((2 : ℂ)⁻¹) •
      (zaunerLeftFactor F x * (zaunerLeftFactor F x')ᴴ)
  have hOff (r s : Fin 2) (i j : Fin 3) (hij : i ≠ j) :
      A (r, i) (s, j) = 0 := by
    dsimp [A]
    rw [Matrix.smul_apply,
      zaunerLeftFactor_mul_conjTranspose_offMode_zero
        F x x' hF r s i j hij]
    simp
  change (2 / 3 : ℝ) ≤
    ∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3,
      (Complex.normSq (A p q) - (1 / 6 : ℝ)) ^ 2
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [hOff, Complex.normSq_zero]
  norm_num
  positivity

/-- Counting only the twenty-four structural zeros in the rational scaled
relative Gram gives the preliminary lower bound twenty-four. -/
theorem zaunerCanonical_scaledRelativeGramDefect_ge_twenty_four
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ)) :
    (24 : ℝ) ≤
      scaledRelativeGramEntrywiseDefect
        (zaunerScaledRelativeGram F x x') := by
  let P : ComplexSquare (Fin 2 × Fin 3) :=
    zaunerScaledRelativeGram F x x'
  have hOff (r s : Fin 2) (i j : Fin 3) (hij : i ≠ j) :
      P (r, i) (s, j) = 0 := by
    exact zaunerScaledRelativeGram_offMode_zero F x x' hF r s i j hij
  change (24 : ℝ) ≤
    ((Fintype.card (Fin 2 × Fin 3) : ℝ)⁻¹) ^ 2 *
      ∑ p : Fin 2 × Fin 3, ∑ q : Fin 2 × Fin 3,
        (Complex.normSq (P p q) -
          (Fintype.card (Fin 2 × Fin 3) : ℝ)) ^ 2
  norm_num only [Fintype.card_prod, Fintype.card_fin, Nat.cast_ofNat]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three]
  simp only [hOff, Complex.normSq_zero]
  norm_num
  positivity

/-- The preliminary zero-count bound transfers to the full potential. -/
theorem zaunerCanonicalCompletion_threeFramePotential_ge_twenty_four
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (X Y : ComplexSquare (Fin 2 × Fin 3)) :
    (24 : ℝ) ≤ completionThreeFramePotential X Y
      (zaunerScaledRelativeGram F x x') := by
  exact le_trans
    (zaunerCanonical_scaledRelativeGramDefect_ge_twenty_four F x x' hF)
    (scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential
      X Y (zaunerScaledRelativeGram F x x'))

/-- Sharp support-face certificate on the scaled-Hadamard row-Gram variety.
The structural zeros leave only two active positions in every row. Row-Gram
mass conservation forces those positions to carry total squared norm `36`,
which raises the normalized defect floor from `24` to `72`. -/
theorem zaunerCanonical_scaledRelativeGramDefect_ge_seventy_two
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (hPGram :
      zaunerScaledRelativeGram F x x' *
          (zaunerScaledRelativeGram F x x')ᴴ =
        (36 : ℂ) • (1 : ComplexSquare (Fin 2 × Fin 3))) :
    (72 : ℝ) ≤
      scaledRelativeGramEntrywiseDefect
        (zaunerScaledRelativeGram F x x') := by
  apply twoModeSupport_scaledRelativeGramDefect_ge_seventy_two
    (zaunerScaledRelativeGram F x x') hPGram
  intro r s i j hij
  exact zaunerScaledRelativeGram_offMode_zero
    F x x' hF r s i j hij

/-- The same sharp margin applies to the complete fixed-edge three-frame
potential. -/
theorem zaunerCanonicalCompletion_threeFramePotential_ge_seventy_two
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (hPGram :
      zaunerScaledRelativeGram F x x' *
          (zaunerScaledRelativeGram F x x')ᴴ =
        (36 : ℂ) • (1 : ComplexSquare (Fin 2 × Fin 3)))
    (X Y : ComplexSquare (Fin 2 × Fin 3)) :
    (72 : ℝ) ≤ completionThreeFramePotential X Y
      (zaunerScaledRelativeGram F x x') := by
  exact le_trans
    (zaunerCanonical_scaledRelativeGramDefect_ge_seventy_two
      F x x' hF hPGram)
    (scaledRelativeGramEntrywiseDefect_le_completionThreeFramePotential
      X Y (zaunerScaledRelativeGram F x x'))

/-- A canonical Zauner scaled relative Gram satisfying its required row-Gram
law cannot lie on the zero locus of the three-frame potential. -/
theorem zaunerCanonicalCompletion_threeFramePotential_ne_zero_of_rowGram
    (F : Matrix (Fin 3) (Fin 3) ℂ)
    (x x' : Fin 3 → ℂ)
    (hF : F * Fᴴ = (1 : Matrix (Fin 3) (Fin 3) ℂ))
    (hPGram :
      zaunerScaledRelativeGram F x x' *
          (zaunerScaledRelativeGram F x x')ᴴ =
        (36 : ℂ) • (1 : ComplexSquare (Fin 2 × Fin 3)))
    (X Y : ComplexSquare (Fin 2 × Fin 3)) :
    completionThreeFramePotential X Y
      (zaunerScaledRelativeGram F x x') ≠ 0 := by
  have hMargin :=
    zaunerCanonicalCompletion_threeFramePotential_ge_seventy_two
      F x x' hF hPGram X Y
  linarith

#print axioms zaunerCanonicalCompletion_normalized_defect_ge_two_thirds
#print axioms zaunerCanonical_scaledRelativeGramDefect_ge_twenty_four
#print axioms zaunerCanonicalCompletion_threeFramePotential_ge_twenty_four
#print axioms zaunerCanonical_scaledRelativeGramDefect_ge_seventy_two
#print axioms zaunerCanonicalCompletion_threeFramePotential_ge_seventy_two
#print axioms zaunerCanonicalCompletion_threeFramePotential_ne_zero_of_rowGram

end D5.S3.Quantum.Tomography.ZaunerAggregateFlatnessCertificate
