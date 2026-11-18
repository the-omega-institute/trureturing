/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows24
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows24
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows24.row_93
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows24
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector94. -/
theorem row_93 : CompatibleFamilyCheck.check good compatible 126 {minimum 93}
    (candidates 93) = true := by decide +kernel
/-- Every full extension with original minimum vector95. -/
theorem row_94 : CompatibleFamilyCheck.check good compatible 126 {minimum 94}
    (candidates 94) = true := by decide +kernel
/-- Every full extension with original minimum vector96. -/
theorem row_95 : CompatibleFamilyCheck.check good compatible 126 {minimum 95}
    (candidates 95) = true := by decide +kernel
/-- Every full extension with original minimum vector97. -/
theorem row_96 : CompatibleFamilyCheck.check good compatible 126 {minimum 96}
    (candidates 96) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows24
