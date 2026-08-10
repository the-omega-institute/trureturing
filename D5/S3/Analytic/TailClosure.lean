/- GID: D5/S3/Analytic/TailClosure
   generality: G
   mirror-B: D5/B/S3/Analytic/TailClosure
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Vanishing tail budgets force certified readings to converge. -/

import D5.S3.Analytic.TailCertificate

open Filter

namespace D5.S3.Analytic.TailClosure

open D5.S3.Analytic.TailCertificate

/- Provenance: thin honest wrapper connecting `Certificate.error_le` to pinned
   mathlib's `squeeze_zero` and `tendsto_iff_dist_tendsto_zero`. -/

/-- A tail certificate over a cofinal family closes analytically when its budget
vanishes: the certified window readings converge to the exact value. -/
theorem vanishing_tail_budget_closes {Atom Window : Type*}
    (family : CofinalWindowFamily Atom Window)
    (control : TailControl Window) (value : Real)
    (certificate : Certificate family control value)
    (windows : Filter Window)
    (budget_vanishes : Tendsto certificate.budget windows (nhds 0)) :
    Tendsto certificate.reading windows (nhds value) := by
  apply tendsto_iff_dist_tendsto_zero.2
  apply squeeze_zero
  · exact fun _ => dist_nonneg
  · intro window
    simpa [Real.dist_eq, abs_sub_comm] using certificate.error_le window
  · exact budget_vanishes

end D5.S3.Analytic.TailClosure
