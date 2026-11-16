/- GID: D5/S3/Combinatorics/Orthogonality/SevenBitParity
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenBitParity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenBitParity.oddPoint_involutive
   digest: Full characteristic-vector parity identities used by the written lower bound. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitGeometry
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitParity
open SevenBitGeometry
/-- Characteristic translation is an involution on the entire original space. -/
theorem oddPoint_involutive : Function.Involutive oddPoint := by
  change ∀ v : Vector, oddPoint (oddPoint v) = v
  decide +kernel
/-- Its parity change uses the original odd dimension. -/
theorem oddPoint_parity : ∀ v : Vector, even (oddPoint v) ↔ ¬ even v := by decide +kernel
/-- It preserves pairing against every even vector. -/
theorem dot_oddPoint : ∀ e ∈ evenPoints, ∀ v : Vector,
    dot e (oddPoint v) = dot e v := by decide +kernel
/-- Every nonzero even point has its full original odd representative. -/
theorem oddPoint_domain : ∀ e ∈ evenPoints,
    oddPoint e ≠ 0 ∧ oddPoint e ≠ 127 ∧ ¬ even (oddPoint e) := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitParity
