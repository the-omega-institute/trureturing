import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace

namespace Reg.D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace

open _root_.D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace

/-- The entire source telescope is retained, including both real family hypotheses.
This is a faithful exact-scope attempt, not a validated four-slot registration.
Whole-source variation and raw source occurrence reconstruction remain unfinished
under the linked same-target issue; no auxiliary readout is fabricated. -/
abbrev sourceScope := type_of% (@literal_closed_compact_open_surjection)

theorem source_actual : sourceScope := @literal_closed_compact_open_surjection

end Reg.D5.S3.Topology.AlmostDisjoint.TaggedCompactSpace
