/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows11
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows11
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows11.row_41
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows11
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector42. -/
theorem row_41 : CompatibleFamilyCheck.check good compatible 126 {minimum 41}
    (candidates 41) = true := by decide +kernel
/-- Every full extension with original minimum vector43. -/
theorem row_42 : CompatibleFamilyCheck.check good compatible 126 {minimum 42}
    (candidates 42) = true := by decide +kernel
/-- Every full extension with original minimum vector44. -/
theorem row_43 : CompatibleFamilyCheck.check good compatible 126 {minimum 43}
    (candidates 43) = true := by decide +kernel
/-- Every full extension with original minimum vector45. -/
theorem row_44 : CompatibleFamilyCheck.check good compatible 126 {minimum 44}
    (candidates 44) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows11
