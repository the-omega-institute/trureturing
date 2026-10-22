/- GID: D5/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial
   generality: I
   mirror-B: D5/B/S3/ConceptDynamics/Spacetime/CopyProfilePolynomial
   mirror-E: none(waiver:stage-a-open)
   anchors: []
   utility: none
   digest: Native time profiles give the full copy polynomial and its finite one-hole slice readout. -/

/- Compatibility exports; mathematical content lives with the native witness. -/
import D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
set_option autoImplicit false
namespace D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
open D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile
export D5.S3.ConceptDynamics.Spacetime.NativeTimeProfile (Bal copies value CopyPolynomialLaw profileCoefficients profile_multiaffine copy_polynomial_law CopiesRegionLinear wordReadout CopySliceReadoutLaw CopySaturationLaw polynomial_identification copies_region_linear copy_saturation_law copy_slice_readout_law sum_word_readouts_implies_tail copy_q_expressible_implies_tail tail_implies_copy_q_expressible CopyQExpressible)
end D5.S3.ConceptDynamics.Spacetime.CopyProfilePolynomial
