/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows04
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows04
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows04.row_13
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows04
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector14. -/
theorem row_13 : CompatibleFamilyCheck.check good compatible 126 {minimum 13}
    (candidates 13) = true := by decide +kernel
/-- Every full extension with original minimum vector15. -/
theorem row_14 : CompatibleFamilyCheck.check good compatible 126 {minimum 14}
    (candidates 14) = true := by decide +kernel
/-- Every full extension with original minimum vector16. -/
theorem row_15 : CompatibleFamilyCheck.check good compatible 126 {minimum 15}
    (candidates 15) = true := by decide +kernel
/-- Every full extension with original minimum vector17. -/
theorem row_16 : CompatibleFamilyCheck.check good compatible 126 {minimum 16}
    (candidates 16) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows04
