/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows08
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows08
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows08.row_29
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows08
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector30. -/
theorem row_29 : CompatibleFamilyCheck.check good compatible 126 {minimum 29}
    (candidates 29) = true := by decide +kernel
/-- Every full extension with original minimum vector31. -/
theorem row_30 : CompatibleFamilyCheck.check good compatible 126 {minimum 30}
    (candidates 30) = true := by decide +kernel
/-- Every full extension with original minimum vector32. -/
theorem row_31 : CompatibleFamilyCheck.check good compatible 126 {minimum 31}
    (candidates 31) = true := by decide +kernel
/-- Every full extension with original minimum vector33. -/
theorem row_32 : CompatibleFamilyCheck.check good compatible 126 {minimum 32}
    (candidates 32) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows08
