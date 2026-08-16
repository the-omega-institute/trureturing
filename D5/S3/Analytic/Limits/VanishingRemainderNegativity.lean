/- GID: D5/S3/Analytic/Limits/VanishingRemainderNegativity
   generality: G
   mirror-B: D5/B/S3/Analytic/Limits/VanishingRemainderNegativity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A negative limit remains eventually negative after adding a vanishing remainder. -/

import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.OrderClosed

/- Library-search audit trail (2026-08-16):
   * D5 searches found no theorem combining a negative limiting contribution with a vanishing
     remainder to obtain eventual negativity.
   * Loogle returned the exact pinned-Mathlib declarations `Filter.Tendsto.add` and
     `Filter.Tendsto.eventually_lt_const`; both are imported and applied below.
   * LeanSearch's `/api/search` endpoint and the tested Reservoir API endpoint returned HTTP 404.
   * GitHub code search returned HTTP 401 without authentication, so it supplied no result. -/

namespace D5.S3.Analytic.Limits.VanishingRemainderNegativity

open Filter Topology

/-- If a main contribution tends to a strictly negative constant and every other contribution
vanishes, then their sum is eventually negative. This is the asymptotic core of the source atom;
the zeta-specific orbit decomposition and test-function construction are not claimed here. -/
theorem vanishing_remainder_eventually_negative
    (main remainder : ℕ -> ℝ) (c : ℝ) (hc : 0 < c)
    (hmain : Tendsto main atTop (𝓝 (-c)))
    (hremainder : Tendsto remainder atTop (𝓝 0)) :
    ∀ᶠ n in atTop, main n + remainder n < 0 := by
  have hsum : Tendsto (fun n => main n + remainder n) atTop (𝓝 (-c + 0)) :=
    hmain.add hremainder
  exact hsum.eventually_lt_const (by simpa using hc)

#print axioms vanishing_remainder_eventually_negative

end D5.S3.Analytic.Limits.VanishingRemainderNegativity
