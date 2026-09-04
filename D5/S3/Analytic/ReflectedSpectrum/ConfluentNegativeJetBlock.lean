/- GID: D5/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock
   generality: G
   mirror-B: D5/B/S3/Analytic/ReflectedSpectrum/ConfluentNegativeJetBlock
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: An invertible jet multiplier transports Hardy positivity to exact negative inertia. -/

import D5.S3.SpectralTopology.FiniteSpectralLocalizer

/-!
# Confluent negative jet block

The analytic argument in the source first removes the positive kernel term on
the first `m` jets and then applies the multiplication Leibniz rule.  Those
steps produce the finite factorization `G = -(Lᴴ * H * L)`, where `H` is the
Hardy derivative-evaluation Gram matrix and `L` is invertible because its
diagonal is the nonzero value of the reflected entire function.

The theorem below isolates the exact finite-dimensional consequence of that
analytic construction.  Congruence by `L` preserves positive definiteness, so
`G` is strictly negative definite.  Its negative index is not merely bounded
below by `m`: it is exactly `m`, closing the source inequality with equality.

Library-search and duplication audit (2026-09-03):

* Keyword and symbol-shape searches under `D5/` found no owner for a
  confluent negative jet block or the factorization `-(Lᴴ * H * L)` together
  with its exact negative index.
* The formalization receipt index and digestion ledgers contain only this
  atom's residual-open entry, not an accepted coverage edge.
* Generalized searches found the reusable inertia owners
  `RHLinalg.negIndex` and `posIndex_neg_eq_negIndex`, but no theorem combining
  them with positive-definite matrix congruence.
* Searches of every remote `origin/lane/math/*` branch found no in-flight
  implementation of this atom or an equivalent theorem.
* Pinned Mathlib supplies
  `Matrix.IsUnit.posDef_star_left_conjugate_iff` and
  `Matrix.PosDef.eigenvalues_pos`; both are applied directly below.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace D5.S3.Analytic.ReflectedSpectrum.ConfluentNegativeJetBlock

open RHLinalg
open D5.S3.SpectralTopology.FiniteSpectralLocalizer

/-- If the first `m` kernel jets factor as the negative of an invertible
congruence of a positive Hardy Gram matrix, the block is strictly negative
definite and has exactly `m` negative eigenvalues. -/
theorem confluent_negative_jet_block
    (m : ℕ) (H L G : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.PosDef) (hL : IsUnit L) (hG : G.IsHermitian)
    (hFactor : G = -(Lᴴ * H * L)) :
    (-G).PosDef ∧ negIndex hG = m := by
  have hCongruence : (Lᴴ * H * L).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff hL).2 hH
  have hNegative : (-G).PosDef := by
    rw [hFactor]
    simpa only [neg_neg]
  refine ⟨hNegative, ?_⟩
  calc
    negIndex hG = posIndex hG.neg :=
      (posIndex_neg_eq_negIndex hG).symm
    _ = Fintype.card (Fin m) := by
      unfold posIndex
      rw [Finset.filter_eq_self.2]
      · exact Finset.card_univ
      · intro i hi
        exact hNegative.eigenvalues_pos i
    _ = m := Fintype.card_fin m

/-- The exact index theorem contains the source's lower bound. -/
theorem confluent_negative_jet_block_index_lower_bound
    (m : ℕ) (H L G : Matrix (Fin m) (Fin m) ℂ)
    (hH : H.PosDef) (hL : IsUnit L) (hG : G.IsHermitian)
    (hFactor : G = -(Lᴴ * H * L)) :
    m ≤ negIndex hG := by
  exact (confluent_negative_jet_block m H L G hH hL hG hFactor).2.ge

/-- A one-jet instance witnesses that the exact negative count is attained. -/
example :
    let H : Matrix (Fin 1) (Fin 1) ℂ := 1
    let L : Matrix (Fin 1) (Fin 1) ℂ := 1
    let G : Matrix (Fin 1) (Fin 1) ℂ := -1
    ∃ hG : G.IsHermitian, negIndex hG = 1 := by
  dsimp only
  have hH : (1 : Matrix (Fin 1) (Fin 1) ℂ).PosDef := Matrix.PosDef.one
  have hL : IsUnit (1 : Matrix (Fin 1) (Fin 1) ℂ) := isUnit_one
  have hG : (-1 : Matrix (Fin 1) (Fin 1) ℂ).IsHermitian :=
    Matrix.isHermitian_one.neg
  refine ⟨hG, (confluent_negative_jet_block 1 1 1 (-1) hH hL hG ?_).2⟩
  simp

#print axioms confluent_negative_jet_block
#print axioms confluent_negative_jet_block_index_lower_bound

end D5.S3.Analytic.ReflectedSpectrum.ConfluentNegativeJetBlock
