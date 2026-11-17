/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows31
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows31
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows31.row_121
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows31
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector122. -/
theorem row_121 : CompatibleFamilyCheck.check good compatible 126 {minimum 121}
    (candidates 121) = true := by decide +kernel
/-- Every full extension with original minimum vector123. -/
theorem row_122 : CompatibleFamilyCheck.check good compatible 126 {minimum 122}
    (candidates 122) = true := by decide +kernel
/-- Every full extension with original minimum vector124. -/
theorem row_123 : CompatibleFamilyCheck.check good compatible 126 {minimum 123}
    (candidates 123) = true := by decide +kernel
/-- Every full extension with original minimum vector125. -/
theorem row_124 : CompatibleFamilyCheck.check good compatible 126 {minimum 124}
    (candidates 124) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows31
