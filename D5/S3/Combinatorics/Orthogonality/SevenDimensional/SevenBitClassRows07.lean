/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows07
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows07
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows07.row_25
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows07
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector26. -/
theorem row_25 : CompatibleFamilyCheck.check good compatible 126 {minimum 25}
    (candidates 25) = true := by decide +kernel
/-- Every full extension with original minimum vector27. -/
theorem row_26 : CompatibleFamilyCheck.check good compatible 126 {minimum 26}
    (candidates 26) = true := by decide +kernel
/-- Every full extension with original minimum vector28. -/
theorem row_27 : CompatibleFamilyCheck.check good compatible 126 {minimum 27}
    (candidates 27) = true := by decide +kernel
/-- Every full extension with original minimum vector29. -/
theorem row_28 : CompatibleFamilyCheck.check good compatible 126 {minimum 28}
    (candidates 28) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows07
