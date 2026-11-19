/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRow00
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRow00
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRow00.row_0
   digest: Complete original compatible classes with the first original minimum vector. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitGeometry
/-! The original full predicate is unchanged. This partitions its proof by
minimum vector to bound kernel memory, without sampling or omitting classes. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRow00
open SevenBitGeometry
/-- Every complete extension of original minimum vector1. -/
theorem row_0 : CompatibleFamilyCheck.check good compatible 126 {(1 : Vector)}
    (deleted.filter (fun v => decide ((1 : Vector) < v) && compatible 1 v)) = true := by
  decide +kernel
#print axioms row_0
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRow00
