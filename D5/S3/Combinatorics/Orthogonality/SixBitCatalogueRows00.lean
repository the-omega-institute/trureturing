/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows00
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueRows00
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.actual_chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows00.checked_rows_00
   digest: First exact row block of the full received six-dimensional certificate. -/
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueData
/-! The entire source certificate is checked in exact row blocks. No row or
pair is omitted; the blocks are consumed by the full Covers/Proper theorem.
Historical native-evaluation provenance stays in the main verification module. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BinaryOrthogonality
/-- Every check in the first ten exact rows, using the sound Boolean traversal. -/
theorem checked_rows_00 : checkAll 10 (dimensionSix.rowCheck) = true := by decide +kernel
end BinaryOrthogonality
