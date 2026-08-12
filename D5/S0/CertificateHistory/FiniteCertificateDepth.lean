/- GID: D5/S0/CertificateHistory/FiniteCertificateDepth
   generality: G
   mirror-B: D5/B/S0/CertificateHistory/FiniteCertificateDepth
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Every event-history certificate references only finitely many generating events. -/

import D5.S0.History.HistoryCarrier
import Mathlib.Data.Set.Finite.Basic

namespace D5.S0.CertificateHistory.FiniteCertificateDepth

open D5.S0.History

/-- Every certificate represented by an event history references only finitely many
generating events. This is the finite-depth consequence of the list-based history carrier. -/
theorem certificate_references_finitely_many_events
    (certificate : EventHistory) :
    Set.Finite {event | event ∈ certificate} :=
  List.finite_toSet certificate

end D5.S0.CertificateHistory.FiniteCertificateDepth
