/- GID: D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows01
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows01
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; instance=D5/S3/Combinatorics/Orthogonality/SevenDimensional/SevenBitClassRows01.row_1
   digest: Complete original compatible classes for four exact minimum vectors. -/
import D5.S3.Combinatorics.Orthogonality.SevenBitClassDomains
/-! Exact complete extensions in the original126-line domain. The same full
predicate is split only to bound kernel reduction memory. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace D5.S3.Combinatorics.Orthogonality.SevenBitClassRows01
open SevenBitGeometry SevenBitClassDomains
/-- Every full extension with original minimum vector2. -/
theorem row_1 : CompatibleFamilyCheck.check good compatible 126 {minimum 1}
    (candidates 1) = true := by decide +kernel
/-- Every full extension with original minimum vector3. -/
theorem row_2 : CompatibleFamilyCheck.check good compatible 126 {minimum 2}
    (candidates 2) = true := by decide +kernel
/-- Every full extension with original minimum vector4. -/
theorem row_3 : CompatibleFamilyCheck.check good compatible 126 {minimum 3}
    (candidates 3) = true := by decide +kernel
/-- Every full extension with original minimum vector5. -/
theorem row_4 : CompatibleFamilyCheck.check good compatible 126 {minimum 4}
    (candidates 4) = true := by decide +kernel
end D5.S3.Combinatorics.Orthogonality.SevenBitClassRows01
