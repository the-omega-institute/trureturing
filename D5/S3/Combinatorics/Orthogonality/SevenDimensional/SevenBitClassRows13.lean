/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows13
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows13
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows13.row_49
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows13
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector50. -/
theorem row_49 : CompatibleFamilyCheck.check good compatible 126 {minimum 49}
    (candidates 49) = true := by decide +kernel
/-- Every full extension with original minimum vector51. -/
theorem row_50 : CompatibleFamilyCheck.check good compatible 126 {minimum 50}
    (candidates 50) = true := by decide +kernel
/-- Every full extension with original minimum vector52. -/
theorem row_51 : CompatibleFamilyCheck.check good compatible 126 {minimum 51}
    (candidates 51) = true := by decide +kernel
/-- Every full extension with original minimum vector53. -/
theorem row_52 : CompatibleFamilyCheck.check good compatible 126 {minimum 52}
    (candidates 52) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows13
