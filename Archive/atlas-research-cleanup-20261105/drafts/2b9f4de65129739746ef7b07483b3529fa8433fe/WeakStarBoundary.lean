import D5.S3.Topology.Measures.FiniteObservationVariation
import Mathlib.MeasureTheory.Measure.Dirac.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory
open D5.S3.Topology.Measures.NormPreservingLifts

-- Together with BoundaryChecks, this verifies the advertised weak-star
-- compact contrast on the same Boolean sequence carrier. It does not replace
-- norm compactness in the theorem or construct a universal sensor budget.
example :
    let K := ℕ → Bool
    letI : MeasurableSpace K := borel K
    letI : BorelSpace K := ⟨rfl⟩
    IsCompact (range (fun a : K × K =>
      (signedFunctional ((Measure.dirac a.1).toSignedMeasure -
        (Measure.dirac a.2).toSignedMeasure)).toWeakDual)) := by
  dsimp only
  let K := ℕ → Bool
  letI : MeasurableSpace K := borel K
  letI : BorelSpace K := ⟨rfl⟩
  apply isCompact_range
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun a : K × K =>
    signedFunctional ((Measure.dirac a.1).toSignedMeasure -
      (Measure.dirac a.2).toSignedMeasure) f)
  simp_rw [signedFunctional_sub_toSignedMeasure, integral_dirac]
  exact (f.continuous.comp continuous_fst).sub (f.continuous.comp continuous_snd)

#check @D5.S3.Topology.Measures.FiniteObservationVariation.exists_uniform_finite_readout_variation
#check @D5.S3.Topology.Measures.NormPreservingLifts.functional_map
#check @D5.S3.Topology.Measures.RegularSignedLift.regular_add
