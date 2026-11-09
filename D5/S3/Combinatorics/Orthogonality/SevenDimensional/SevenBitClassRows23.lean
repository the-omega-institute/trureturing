/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows23
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows23
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows23.row_89
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows23
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector90. -/
theorem row_89 : CompatibleFamilyCheck.check good compatible 126 {minimum 89}
    (candidates 89) = true := by decide +kernel
/-- Every full extension with original minimum vector91. -/
theorem row_90 : CompatibleFamilyCheck.check good compatible 126 {minimum 90}
    (candidates 90) = true := by decide +kernel
/-- Every full extension with original minimum vector92. -/
theorem row_91 : CompatibleFamilyCheck.check good compatible 126 {minimum 91}
    (candidates 91) = true := by decide +kernel
/-- Every full extension with original minimum vector93. -/
theorem row_92 : CompatibleFamilyCheck.check good compatible 126 {minimum 92}
    (candidates 92) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows23
