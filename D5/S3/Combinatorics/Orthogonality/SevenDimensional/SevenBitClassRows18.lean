/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows18
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows18
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows18.row_69
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows18
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector70. -/
theorem row_69 : CompatibleFamilyCheck.check good compatible 126 {minimum 69}
    (candidates 69) = true := by decide +kernel
/-- Every full extension with original minimum vector71. -/
theorem row_70 : CompatibleFamilyCheck.check good compatible 126 {minimum 70}
    (candidates 70) = true := by decide +kernel
/-- Every full extension with original minimum vector72. -/
theorem row_71 : CompatibleFamilyCheck.check good compatible 126 {minimum 71}
    (candidates 71) = true := by decide +kernel
/-- Every full extension with original minimum vector73. -/
theorem row_72 : CompatibleFamilyCheck.check good compatible 126 {minimum 72}
    (candidates 72) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows18
