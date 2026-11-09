/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows15
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows15
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows15.row_57
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows15
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector58. -/
theorem row_57 : CompatibleFamilyCheck.check good compatible 126 {minimum 57}
    (candidates 57) = true := by decide +kernel
/-- Every full extension with original minimum vector59. -/
theorem row_58 : CompatibleFamilyCheck.check good compatible 126 {minimum 58}
    (candidates 58) = true := by decide +kernel
/-- Every full extension with original minimum vector60. -/
theorem row_59 : CompatibleFamilyCheck.check good compatible 126 {minimum 59}
    (candidates 59) = true := by decide +kernel
/-- Every full extension with original minimum vector61. -/
theorem row_60 : CompatibleFamilyCheck.check good compatible 126 {minimum 60}
    (candidates 60) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows15
