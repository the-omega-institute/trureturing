/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows22
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows22
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows22.row_85
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows22
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector86. -/
theorem row_85 : CompatibleFamilyCheck.check good compatible 126 {minimum 85}
    (candidates 85) = true := by decide +kernel
/-- Every full extension with original minimum vector87. -/
theorem row_86 : CompatibleFamilyCheck.check good compatible 126 {minimum 86}
    (candidates 86) = true := by decide +kernel
/-- Every full extension with original minimum vector88. -/
theorem row_87 : CompatibleFamilyCheck.check good compatible 126 {minimum 87}
    (candidates 87) = true := by decide +kernel
/-- Every full extension with original minimum vector89. -/
theorem row_88 : CompatibleFamilyCheck.check good compatible 126 {minimum 88}
    (candidates 88) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows22
