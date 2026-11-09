/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows28
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows28
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows28.row_109
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows28
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector110. -/
theorem row_109 : CompatibleFamilyCheck.check good compatible 126 {minimum 109}
    (candidates 109) = true := by decide +kernel
/-- Every full extension with original minimum vector111. -/
theorem row_110 : CompatibleFamilyCheck.check good compatible 126 {minimum 110}
    (candidates 110) = true := by decide +kernel
/-- Every full extension with original minimum vector112. -/
theorem row_111 : CompatibleFamilyCheck.check good compatible 126 {minimum 111}
    (candidates 111) = true := by decide +kernel
/-- Every full extension with original minimum vector113. -/
theorem row_112 : CompatibleFamilyCheck.check good compatible 126 {minimum 112}
    (candidates 112) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows28
