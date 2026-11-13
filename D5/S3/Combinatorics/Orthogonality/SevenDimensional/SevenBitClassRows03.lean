/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows03
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows03
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows03.row_9
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows03
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector10. -/
theorem row_9 : CompatibleFamilyCheck.check good compatible 126 {minimum 9}
    (candidates 9) = true := by decide +kernel
/-- Every full extension with original minimum vector11. -/
theorem row_10 : CompatibleFamilyCheck.check good compatible 126 {minimum 10}
    (candidates 10) = true := by decide +kernel
/-- Every full extension with original minimum vector12. -/
theorem row_11 : CompatibleFamilyCheck.check good compatible 126 {minimum 11}
    (candidates 11) = true := by decide +kernel
/-- Every full extension with original minimum vector13. -/
theorem row_12 : CompatibleFamilyCheck.check good compatible 126 {minimum 12}
    (candidates 12) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows03
