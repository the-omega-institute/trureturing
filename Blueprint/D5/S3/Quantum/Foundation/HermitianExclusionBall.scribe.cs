using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class HermitianExclusionBallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A complex orthogonal two-plane gives global affine Bloch coordinates on the entire original mixed-state exclusion.",
        H("Entire exclusion balls from full complex frames"),
        Blocks(
            Paragraph(Text("The carrier is all complex Hermitian three by three matrices, the cone is the full positive semidefinite cone, and the unit is the trace. All original proper real-linear effects remain available. Let v be any unit complex vector and let W be a three by two complex matrix with W*W=I and WW*=I-vv*. These hypotheses identify the whole orthogonal complement of v, rather than a selected subspace of it.")),
            Describe.Lean(DescribeId.Create("full-frame-chart"),
                DeclarationHandle.Create("D5/S3/Quantum/Foundation/HermitianExclusionBall.chart_of_full_frame"),
                H("Global affine chart of the entire exclusion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every v of norm one and every W satisfying W*W=I and WW*=I-vv*, there exists a native ExclusionChart for the original exclusion of vv*, with dimension exactly three. Its parameter map is defined on the whole real Euclidean three-space by r |-> W blochMatrix(1,r) W*. It is affine and injective on that entire space. The image of the closed unit ball equals the entire original exclusion, with no rank restriction on mixed states."))),
                DescribeRole.Theorem),
            Paragraph(Text("Compression by W* inverts the parameter map globally because W*W=I; the existing Bloch coordinate inverse proves injectivity. Conjugation preserves positivity and cyclicity of trace preserves normalization. Conversely, the full proper-functional exclusion identity gives Xv=0. Hermitian symmetry gives v*X=0, so X=(I-vv*)X(I-vv*). Consequently X=W(W*XW)W*. The compression is positive and trace one. The full two by two Bloch ball characterization supplies a coordinate of norm at most one, and reconstruction gives exactly X.")),
            Paragraph(Text("The frame hypotheses concern actual complex matrices. This statement supplies neither their existence for every original pure label nor a complete original EB3 hypothesis term. Physical realization and literature priority are not asserted.")))));
}
