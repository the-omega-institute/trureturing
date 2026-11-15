/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows06
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows06
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows06.row_21
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows06
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector22. -/
theorem row_21 : CompatibleFamilyCheck.check good compatible 126 {minimum 21}
    (candidates 21) = true := by decide +kernel
/-- Every full extension with original minimum vector23. -/
theorem row_22 : CompatibleFamilyCheck.check good compatible 126 {minimum 22}
    (candidates 22) = true := by decide +kernel
/-- Every full extension with original minimum vector24. -/
theorem row_23 : CompatibleFamilyCheck.check good compatible 126 {minimum 23}
    (candidates 23) = true := by decide +kernel
/-- Every full extension with original minimum vector25. -/
theorem row_24 : CompatibleFamilyCheck.check good compatible 126 {minimum 24}
    (candidates 24) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows06
