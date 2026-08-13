/- GID: D5/S3/Zeros/Endpoints/XiEndpointValues
   generality: I
   mirror-B: D5/B/S3/Zeros/Endpoints/XiEndpointValues
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: The pole-removed completed-zeta xi reading has value one-half at both endpoints. -/

import D5.S3.Zeros.CompletedZeta

namespace D5.S3.Zeros.Endpoints.XiEndpointValues

open D5.S3.Zeros.CompletedZeta

/-- The pole-removed completed-zeta xi reading takes the value `1 / 2` at both endpoints.

Both values are definitionally immediate from the frozen pole-removed reading. -/
theorem xi_reading_endpoint_values :
    xiReading 0 = (1 / 2 : ℂ) ∧ xiReading 1 = (1 / 2 : ℂ) := by
  norm_num [xiReading]

end D5.S3.Zeros.Endpoints.XiEndpointValues
