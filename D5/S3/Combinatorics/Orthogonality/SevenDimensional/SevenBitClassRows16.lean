/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows16
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows16
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows16.row_61
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows16
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector62. -/
theorem row_61 : CompatibleFamilyCheck.check good compatible 126 {minimum 61}
    (candidates 61) = true := by decide +kernel
/-- Every full extension with original minimum vector63. -/
theorem row_62 : CompatibleFamilyCheck.check good compatible 126 {minimum 62}
    (candidates 62) = true := by decide +kernel
/-- Every full extension with original minimum vector64. -/
theorem row_63 : CompatibleFamilyCheck.check good compatible 126 {minimum 63}
    (candidates 63) = true := by decide +kernel
/-- Every full extension with original minimum vector65. -/
theorem row_64 : CompatibleFamilyCheck.check good compatible 126 {minimum 64}
    (candidates 64) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows16
