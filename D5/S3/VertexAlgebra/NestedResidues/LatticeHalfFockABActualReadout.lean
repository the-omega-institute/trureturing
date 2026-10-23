/- GID: D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout
   generality: I
   mirror-B: D5/B/S3/VertexAlgebra/NestedResidues/LatticeHalfFockABActualReadout
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual source/source nested extraction at independent finite cutoffs. -/

import D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABLocalResidue

/-! Supported extraction keeps the actual inner cutoff independent of the
finite Laurent supplier and retains the original current/source labels. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
open LatticeHalfFockLeftCurrentTransport LatticeHalfFockNestedQReadout
open LatticeHalfFockClearedTaylorReadout LatticeHalfFockABLocalResidue
open LatticeHalfFockSliceQuotient UniformGradedLocalCorrelator
open LatticeGeneratingFieldLocality LatticeHalfFockChargedTensorCoefficients
open LatticeSugawaraCurrents LatticeFiniteNegativeGeneration
open CollisionRationalExpansions.OrderedRationalExpansion
open SupportedFieldWords.OrderedWords
open OrderedCollisionCoordinates.OrderedCoefficientCompatibility
open scoped BigOperators VertexOperator
noncomputable section

/- proof_shape: actual_ab_nested_readout: content
   admission_basis: escape-witness
   escape_witness: The supplier six-word coefficients on total mode degree
   d+r+n are transported through the actual homogeneous quotient comparison.
   Nested supported extraction then retains an independent inner cutoff I,
   including I=K, rather than comparing cutoff-dependent actual fields. -/
set_option maxHeartbeats 1600000 in
-- Retain the complete dependent homogeneous telescope during extraction.
/-- The actual finite nested Q field, with arbitrary inner cutoff I, is the
supported readout of the complete A/B rational G at the original numerator P,K.
No locality at K or I is assumed. The support is on complete outer fibers. -/
theorem actual_ab_nested_readout
    (D : LatticeData) (hu : IsUnit D.G.det) (i : Fin D.rank)
    (a b : Carrier D) (K I H : ℕ) (gamma delta d r n j : ℤ)
    (x : ActualTensor D hu) (phi : ActualTensor D hu →ₗ[ℂ] ℂ)
    (P : LabelledPolynomial ℂ 3)
    (coefficients : ∀ e : Exponent 3, P.coeff e =
      if totalExponent e =
          (∑ p ∈ labelledPairs 3, (threeOrders D a b K p : ℤ)) - d - r - n - 3
      then phi (actualNumerator D hu i a b gamma delta K x e) else 0) :
    NestedRightSupported gamma (r + j) (d - j) n I H
      (rationalTripleReadout D a b K P) ∧
    phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n I H
        (originalRational D a b K P) ∧
    phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      supportedQReadout 1 (d - j) H n
        (fun k l =>
          (coefficientHahn ℂ 2 0 (1 : Fin 3) (finSuccAboveEquiv 1)
            (completeAB gamma (r + j) I (originalRational D a b K P))).coeff
              (exponents 2 ![-k - 1, -l - 1]))
        (fun k l =>
          (coefficientHahn ℂ 1 1 (1 : Fin 3)
            ((Equiv.swap 0 1).trans (finSuccAboveEquiv 1))
            (completeAB gamma (r + j) I (originalRational D a b K P))).coeff
              (exponents 2 ![-k - 1, -l - 1])) := by
  obtain ⟨K₀, supplier⟩ := actual_finite_laurent_carriers D hu i a b
  let total := (∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ)) - d - r - n - 3
  obtain ⟨P₀, coefficients₀, words⟩ := supplier gamma delta x phi total
  have quotient := (actual_slice_quotient_compat D hu i a b K K₀ gamma delta d r n
    x phi P P₀ coefficients coefficients₀).2.1
  have same (order : Fin 6) (modes : Exponent 3)
      (degree : (∑ k, modes k) = (r + j) + (d - j) + n) :
      tripleScalar (targetCurrent D hu i) (targetSlice D hu a gamma)
        (targetSlice D hu b delta) x phi order modes =
      rationalTripleReadout D a b K P order modes := by
    have index : totalExponent (fun k => -modes k - 1) =
        total - ∑ p ∈ labelledPairs 3, (threeOrders D a b K₀ p : ℤ) := by
      simp only [totalExponent, Fin.sum_univ_three] at degree ⊢
      dsimp [total]
      omega
    have readout := words (triplePermutation order) (fun k => -modes k - 1)
    rw [ite_eq_left index, ← quotient] at readout
    exact readout.symm
  have identified : phi (((qField 1 (d - j) H (targetCurrent D hu i)
      (qField gamma (r + j) I (targetSlice D hu a gamma)
        (targetSlice D hu b delta)))[[n]]) x) =
      nestedRightLocalReadout 1 1 gamma (r + j) (d - j) n I H
        (originalRational D a b K P) := by
    rw [supportedNestedRightReadout_eq]
    rw [supportedNestedRightReadout_congr _ _ _ _ _ _ _ _ _ same]
    change supportedNestedRightReadout 1 gamma (r + j) (d - j) n I H
      (hahnTripleScalar (rationalTripleCarriers D a b K P)) = _
    rw [← nestedRightFiberReadout_eq]
    exact nestedRightLocalReadout_sourceSource D a b K I P 1 gamma (r + j) (d - j) n H
  refine ⟨(NestedRightSupported_congr _ _ _ _ _ _ _ _ same).mp
    (actual_nested_right_support _ _ _ _ _ _ _ _ _ x phi), identified, ?_⟩
  rw [identified]
  unfold nestedRightLocalReadout
  apply supportedQReadout_congr
  · intro k l _
    exact (ab_complete_remaining_orders D a b K I P gamma (r + j) l k).2.2.1
  · intro k l _
    exact (ab_complete_remaining_orders D a b K I P gamma (r + j) k l).2.2.2

end
end D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockABActualReadout
