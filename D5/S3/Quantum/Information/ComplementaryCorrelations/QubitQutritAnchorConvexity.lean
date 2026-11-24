/- GID: D5/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity
   generality: I
   mirror-B: D5/B/S3/Quantum/Information/ComplementaryCorrelations/QubitQutritAnchorConvexity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Product-anchor convexity for all qubit–qutrit local MUB pairs. -/

import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMUBNormalForm
import D5.S3.Quantum.Information.ComplementaryCorrelations.AnchorMeasurementCovariance
import D5.S3.Quantum.Information.ComplementaryCorrelations.Certificate.CovarianceMatrixAdapter

/-! Nonnegativity of Qian’s anchor quadratic in dimensions two and three. -/

namespace AnchorMeasurement

open scoped ComplexOrder
open MUBNormalForm

/-- Qian, Definition 7.2 and equation (39), in the dimensions of §11(1).
The anchor quadratic is nonnegative along every Hermitian direction with
zero partial traces, at every faithful qubit–qutrit product state and for
every pair of mutually unbiased local bases on each subsystem. -/
theorem qubit_qutrit_anchor_convexity : ACC₂₃AllBases := by
  intro UQ UR VQ VR hA hB α β hα hβ D hD
  obtain ⟨W, Z, he⟩ := anchorQuadraticIn_eq_standard UQ UR VQ VR hA hB
  have hα' : (densityMatrix (stateInBasis W α)).PosDef := by
    rw [densityMatrix_stateInBasis]
    exact inBasis_posDef W hα
  have hβ' : (densityMatrix (stateInBasis Z β)).PosDef := by
    rw [densityMatrix_stateInBasis]
    exact inBasis_posDef Z hβ
  rw [he α β D]
  exact acc₂₃_of_raw_diagonal_circulant QianACC.CovarianceMatrixAdapter.bob_raw_covariance
    (stateInBasis W α) (stateInBasis Z β) hα' hβ'
    (inBasis (productBasis W Z) D) (marginalFree_inBasis W Z hD)

end AnchorMeasurement
