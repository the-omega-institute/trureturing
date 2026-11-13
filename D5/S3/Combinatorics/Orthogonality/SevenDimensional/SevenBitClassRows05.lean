/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows05
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows05
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows05.row_17
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows05
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector18. -/
theorem row_17 : CompatibleFamilyCheck.check good compatible 126 {minimum 17}
    (candidates 17) = true := by decide +kernel
/-- Every full extension with original minimum vector19. -/
theorem row_18 : CompatibleFamilyCheck.check good compatible 126 {minimum 18}
    (candidates 18) = true := by decide +kernel
/-- Every full extension with original minimum vector20. -/
theorem row_19 : CompatibleFamilyCheck.check good compatible 126 {minimum 19}
    (candidates 19) = true := by decide +kernel
/-- Every full extension with original minimum vector21. -/
theorem row_20 : CompatibleFamilyCheck.check good compatible 126 {minimum 20}
    (candidates 20) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows05
