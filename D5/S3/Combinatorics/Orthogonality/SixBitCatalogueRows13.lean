/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows13
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueRows13
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.actual_chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows13.checked_rows_13
   digest: Exact rows 778 through 841 of the complete received six-dimensional certificate. -/
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueData
/-! Lossless row partition of every original covering, perpendicular and
same-color pair predicate. Full checks retain every row, vector and pair. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BinaryOrthogonality
/-- All original checks at each exact index in this block. -/
theorem checked_rows_13 :
    checkAll 64 (fun i => dimensionSix.rowCheck (778+i)) = true := by decide +kernel
end BinaryOrthogonality
