/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows10
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows10
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows10.row_37
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows10
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector38. -/
theorem row_37 : CompatibleFamilyCheck.check good compatible 126 {minimum 37}
    (candidates 37) = true := by decide +kernel
/-- Every full extension with original minimum vector39. -/
theorem row_38 : CompatibleFamilyCheck.check good compatible 126 {minimum 38}
    (candidates 38) = true := by decide +kernel
/-- Every full extension with original minimum vector40. -/
theorem row_39 : CompatibleFamilyCheck.check good compatible 126 {minimum 39}
    (candidates 39) = true := by decide +kernel
/-- Every full extension with original minimum vector41. -/
theorem row_40 : CompatibleFamilyCheck.check good compatible 126 {minimum 40}
    (candidates 40) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows10
