/- GID: D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows10
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/SixBitCatalogueRows10
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueVerification.actual_chromatic_number_six; instance=D5/S3/Combinatorics/Orthogonality/SixBitCatalogueRows10.checked_rows_10
   digest: Exact rows 586 through 649 of the complete received six-dimensional certificate. -/
import D5.S3.Combinatorics.Orthogonality.SixBitCatalogueData
/-! Lossless row partition of every original covering, perpendicular and
same-color pair predicate. Full checks retain every row, vector and pair. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BinaryOrthogonality
/-- All original checks at each exact index in this block. -/
theorem checked_rows_10 :
    checkAll 64 (fun i => dimensionSix.rowCheck (586+i)) = true := by decide +kernel
end BinaryOrthogonality
