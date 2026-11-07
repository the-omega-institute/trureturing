using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit.MersenneExceptional19UpperBasis;

internal sealed class CorrectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer correction incidence before torsion-sensitive descent — UNCOMPILED source preparation.",
        H("Integer correction incidence before torsion-sensitive descent"),
        Blocks(
            Paragraph(Text("The physical correction vector. The six nonzero entries of C are C_(1,d-3)=1, C_(1,d-2)=1, C_(2,d-2)=-1, C_(0,d-1)=-1, C_(1,d-1)=2 and C_(2,d-1)=-2. correctionBlock expresses C*theta by reusing the sealed first, middle and last normal-form functions with zero geometric generators. correctedBlock subtracts it from the original physical block labels. highTheta is exactly 2*g_(d-3)-g_(d-2).")),
            Paragraph(Text("Integer incidence, then arbitrary groups. The shared physical readouts and top_digits prove that reading correctionBlock on chi(L,M,U) equals correction(B,L,M,U)*theta. For a permitted affine row, the sealed affine_digits theorem already proves correction=0 in Z. affine_correction_integer_zero records this actual integer incidence, and corrected_affine_read consumes it to preserve the affine readout for arbitrary A. This reuses the stronger existing integer digit fact directly; it performs no cancellation of Q, 2 or any other scalar inside A.")),
            Paragraph(Text("Starting the descent. The six actual high equations from HighRows show that at levels d-3,d-2,d-1, the corrected blocks equal a single triple, twice that triple and four times that triple, with its sum zero. These are the initial invariants used by selected_corrected_ladders. They are derived from the selected presentation, rather than requested as assumptions in the final reconstruction.")),
            Paragraph(Text("Evidence boundary. All proofs and their sealed additive prerequisites are UNCOMPILED. No registration, normal-build result, kernel validation or official acceptance follows from this source preparation."))), []));
}
