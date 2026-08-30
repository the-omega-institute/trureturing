/- GID: D5/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/GovernanceFixedPoint/TailSpanPrefixExtension
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: Tail spans preserve prefix extension from an offset in the old document. -/

import D5.S3.ConceptDynamics.GovernanceFixedPoint.Core

/- Library-search audit trail (2026-08-30):
   * Exact searches for `tail_span_prefix_extension` found no declaration in
     D5 or pinned Mathlib.
   * Shape searches for `PrefixExtension` over two `TailBytes` values found
     only the carrier clauses in the frozen GFPT Core module.
   * Pinned Mathlib supplies `List.drop_append_of_le_length`, which transports
     the source suffix through the common tail start. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace D5.S3.ConceptDynamics.GovernanceFixedPoint

/-- Dropping the same valid old-document offset preserves prefix extension. -/
theorem tail_span_prefix_extension
    {Byte : Type u}
    (oldDocument newDocument : List Byte)
    (start : Nat)
    (hprefix : PrefixExtension oldDocument newDocument)
    (hstart : start ≤ oldDocument.length) :
    PrefixExtension
      (TailBytes oldDocument start)
      (TailBytes newDocument start) := by
  rcases hprefix with ⟨suffix, rfl⟩
  refine ⟨suffix, ?_⟩
  exact List.drop_append_of_le_length hstart

#print axioms tail_span_prefix_extension

-- Concrete elaboration witnesses for domain inhabitance and satisfiable hypotheses.
example : List Bool := [false]

example : PrefixExtension ([false] : List Bool) [false, true] := by
  exact ⟨[true], rfl⟩

example :
    PrefixExtension
      (TailBytes ([false] : List Bool) 0)
      (TailBytes [false, true] 0) := by
  exact tail_span_prefix_extension
    [false] [false, true] 0 ⟨[true], rfl⟩ (Nat.zero_le _)

end D5.S3.ConceptDynamics.GovernanceFixedPoint
