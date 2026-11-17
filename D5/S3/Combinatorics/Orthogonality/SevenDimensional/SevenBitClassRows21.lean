/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows21
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows21
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows21.row_81
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows21
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector82. -/
theorem row_81 : CompatibleFamilyCheck.check good compatible 126 {minimum 81}
    (candidates 81) = true := by decide +kernel
/-- Every full extension with original minimum vector83. -/
theorem row_82 : CompatibleFamilyCheck.check good compatible 126 {minimum 82}
    (candidates 82) = true := by decide +kernel
/-- Every full extension with original minimum vector84. -/
theorem row_83 : CompatibleFamilyCheck.check good compatible 126 {minimum 83}
    (candidates 83) = true := by decide +kernel
/-- Every full extension with original minimum vector85. -/
theorem row_84 : CompatibleFamilyCheck.check good compatible 126 {minimum 84}
    (candidates 84) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows21
