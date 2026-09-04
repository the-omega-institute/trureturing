/- GID: D5/S3/Quantum/Tomography/ZaunerAggregateFlatnessCertificate
   generality: G
   mirror-B: D5/B/S3/Quantum/Tomography/ZaunerAggregateFlatnessCertificate
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: All twenty-four off-mode zeros of a canonical order-six Zauner transition aggregate to a normalized defect margin two-thirds and a scaled-relative-Gram three-frame margin twenty-four. -/

import D5.S3.Quantum.Tomography.MUBCompletionThreeFramePotential

/- Library-search audit trail (2026-09-04):
   * Reuses the correct fixed-edge structural-zero theorem, the normalized
     scalar defect, and the scaled-relative-Gram three-frame potential.
   * Reuses `Fintype.sum_prod_type`, `Fin.sum_univ_two`, and
     `Fin.sum_univ_three` to enumerate the exact order-six carrier. No new
     zero-count or matrix carrier is introduced.
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

/-- In the rational scaled-relative-Gram coordinate `P = 6 M`, each of the
same twenty-four structural zeros contributes one full unit. Hence the first
term of the three-frame potential is at least twenty-four. -/
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

/-- Strong canonical-branch certificate: the complete three-frame potential
has margin at least twenty-four. -/
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

#print axioms zaunerCanonicalCompletion_normalized_defect_ge_two_thirds
#print axioms zaunerCanonical_scaledRelativeGramDefect_ge_twenty_four
#print axioms zaunerCanonicalCompletion_threeFramePotential_ge_twenty_four

end D5.S3.Quantum.Tomography.ZaunerAggregateFlatnessCertificate
