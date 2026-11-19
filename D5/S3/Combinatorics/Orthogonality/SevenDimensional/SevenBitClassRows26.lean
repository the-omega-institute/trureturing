/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows26
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows26
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows26.row_101
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows26
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector102. -/
theorem row_101 : CompatibleFamilyCheck.check good compatible 126 {minimum 101}
    (candidates 101) = true := by decide +kernel
/-- Every full extension with original minimum vector103. -/
theorem row_102 : CompatibleFamilyCheck.check good compatible 126 {minimum 102}
    (candidates 102) = true := by decide +kernel
/-- Every full extension with original minimum vector104. -/
theorem row_103 : CompatibleFamilyCheck.check good compatible 126 {minimum 103}
    (candidates 103) = true := by decide +kernel
/-- Every full extension with original minimum vector105. -/
theorem row_104 : CompatibleFamilyCheck.check good compatible 126 {minimum 104}
    (candidates 104) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows26
