/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows17
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows17
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows17.row_65
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows17
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector66. -/
theorem row_65 : CompatibleFamilyCheck.check good compatible 126 {minimum 65}
    (candidates 65) = true := by decide +kernel
/-- Every full extension with original minimum vector67. -/
theorem row_66 : CompatibleFamilyCheck.check good compatible 126 {minimum 66}
    (candidates 66) = true := by decide +kernel
/-- Every full extension with original minimum vector68. -/
theorem row_67 : CompatibleFamilyCheck.check good compatible 126 {minimum 67}
    (candidates 67) = true := by decide +kernel
/-- Every full extension with original minimum vector69. -/
theorem row_68 : CompatibleFamilyCheck.check good compatible 126 {minimum 68}
    (candidates 68) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows17
