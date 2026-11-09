/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows27
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows27
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows27.row_105
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows27
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector106. -/
theorem row_105 : CompatibleFamilyCheck.check good compatible 126 {minimum 105}
    (candidates 105) = true := by decide +kernel
/-- Every full extension with original minimum vector107. -/
theorem row_106 : CompatibleFamilyCheck.check good compatible 126 {minimum 106}
    (candidates 106) = true := by decide +kernel
/-- Every full extension with original minimum vector108. -/
theorem row_107 : CompatibleFamilyCheck.check good compatible 126 {minimum 107}
    (candidates 107) = true := by decide +kernel
/-- Every full extension with original minimum vector109. -/
theorem row_108 : CompatibleFamilyCheck.check good compatible 126 {minimum 108}
    (candidates 108) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows27
