/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows29
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows29
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows29.row_113
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows29
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector114. -/
theorem row_113 : CompatibleFamilyCheck.check good compatible 126 {minimum 113}
    (candidates 113) = true := by decide +kernel
/-- Every full extension with original minimum vector115. -/
theorem row_114 : CompatibleFamilyCheck.check good compatible 126 {minimum 114}
    (candidates 114) = true := by decide +kernel
/-- Every full extension with original minimum vector116. -/
theorem row_115 : CompatibleFamilyCheck.check good compatible 126 {minimum 115}
    (candidates 115) = true := by decide +kernel
/-- Every full extension with original minimum vector117. -/
theorem row_116 : CompatibleFamilyCheck.check good compatible 126 {minimum 116}
    (candidates 116) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows29
