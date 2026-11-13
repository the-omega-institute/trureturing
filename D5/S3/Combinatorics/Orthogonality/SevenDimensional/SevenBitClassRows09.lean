/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows09
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows09
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows09.row_33
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows09
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector34. -/
theorem row_33 : CompatibleFamilyCheck.check good compatible 126 {minimum 33}
    (candidates 33) = true := by decide +kernel
/-- Every full extension with original minimum vector35. -/
theorem row_34 : CompatibleFamilyCheck.check good compatible 126 {minimum 34}
    (candidates 34) = true := by decide +kernel
/-- Every full extension with original minimum vector36. -/
theorem row_35 : CompatibleFamilyCheck.check good compatible 126 {minimum 35}
    (candidates 35) = true := by decide +kernel
/-- Every full extension with original minimum vector37. -/
theorem row_36 : CompatibleFamilyCheck.check good compatible 126 {minimum 36}
    (candidates 36) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows09
