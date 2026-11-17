/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows20
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows20
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows20.row_77
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows20
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector78. -/
theorem row_77 : CompatibleFamilyCheck.check good compatible 126 {minimum 77}
    (candidates 77) = true := by decide +kernel
/-- Every full extension with original minimum vector79. -/
theorem row_78 : CompatibleFamilyCheck.check good compatible 126 {minimum 78}
    (candidates 78) = true := by decide +kernel
/-- Every full extension with original minimum vector80. -/
theorem row_79 : CompatibleFamilyCheck.check good compatible 126 {minimum 79}
    (candidates 79) = true := by decide +kernel
/-- Every full extension with original minimum vector81. -/
theorem row_80 : CompatibleFamilyCheck.check good compatible 126 {minimum 80}
    (candidates 80) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows20
