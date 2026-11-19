/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows02
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows02
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows02.row_5
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows02
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector6. -/
theorem row_5 : CompatibleFamilyCheck.check good compatible 126 {minimum 5}
    (candidates 5) = true := by decide +kernel
/-- Every full extension with original minimum vector7. -/
theorem row_6 : CompatibleFamilyCheck.check good compatible 126 {minimum 6}
    (candidates 6) = true := by decide +kernel
/-- Every full extension with original minimum vector8. -/
theorem row_7 : CompatibleFamilyCheck.check good compatible 126 {minimum 7}
    (candidates 7) = true := by decide +kernel
/-- Every full extension with original minimum vector9. -/
theorem row_8 : CompatibleFamilyCheck.check good compatible 126 {minimum 8}
    (candidates 8) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows02
