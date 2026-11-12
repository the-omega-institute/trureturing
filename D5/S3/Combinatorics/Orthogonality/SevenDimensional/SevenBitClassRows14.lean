/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows14
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows14
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows14.row_53
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows14
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector54. -/
theorem row_53 : CompatibleFamilyCheck.check good compatible 126 {minimum 53}
    (candidates 53) = true := by decide +kernel
/-- Every full extension with original minimum vector55. -/
theorem row_54 : CompatibleFamilyCheck.check good compatible 126 {minimum 54}
    (candidates 54) = true := by decide +kernel
/-- Every full extension with original minimum vector56. -/
theorem row_55 : CompatibleFamilyCheck.check good compatible 126 {minimum 55}
    (candidates 55) = true := by decide +kernel
/-- Every full extension with original minimum vector57. -/
theorem row_56 : CompatibleFamilyCheck.check good compatible 126 {minimum 56}
    (candidates 56) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows14
