/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows19
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows19
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows19.row_73
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows19
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector74. -/
theorem row_73 : CompatibleFamilyCheck.check good compatible 126 {minimum 73}
    (candidates 73) = true := by decide +kernel
/-- Every full extension with original minimum vector75. -/
theorem row_74 : CompatibleFamilyCheck.check good compatible 126 {minimum 74}
    (candidates 74) = true := by decide +kernel
/-- Every full extension with original minimum vector76. -/
theorem row_75 : CompatibleFamilyCheck.check good compatible 126 {minimum 75}
    (candidates 75) = true := by decide +kernel
/-- Every full extension with original minimum vector77. -/
theorem row_76 : CompatibleFamilyCheck.check good compatible 126 {minimum 76}
    (candidates 76) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows19
