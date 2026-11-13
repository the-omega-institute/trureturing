/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows32
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows32
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows32.row_125
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows32
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector126. -/
theorem row_125 : CompatibleFamilyCheck.check good compatible 126 {minimum 125}
    (candidates 125) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows32
