/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows12
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows12
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows12.row_45
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows12
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector46. -/
theorem row_45 : CompatibleFamilyCheck.check good compatible 126 {minimum 45}
    (candidates 45) = true := by decide +kernel
/-- Every full extension with original minimum vector47. -/
theorem row_46 : CompatibleFamilyCheck.check good compatible 126 {minimum 46}
    (candidates 46) = true := by decide +kernel
/-- Every full extension with original minimum vector48. -/
theorem row_47 : CompatibleFamilyCheck.check good compatible 126 {minimum 47}
    (candidates 47) = true := by decide +kernel
/-- Every full extension with original minimum vector49. -/
theorem row_48 : CompatibleFamilyCheck.check good compatible 126 {minimum 48}
    (candidates 48) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows12
