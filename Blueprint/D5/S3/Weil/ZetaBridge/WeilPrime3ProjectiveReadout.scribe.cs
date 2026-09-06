using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaBridge;

internal sealed class WeilPrime3ProjectiveReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact arithmetic and conditional complex-domain consumption of the existing prime-three certificate constants.",
        H("Prime-Three Projective Readout"),
        Blocks(
            Describe.Lean(DescribeId.Create("budget-arithmetic"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilPrime3ProjectiveReadout.prime3_budget_arithmetic"), H("Exact certificate arithmetic"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The three rational enclosure inputs from PR #5602 give the exact projective budget 15303/16495000, strictly below (61/2000)^2. This proves arithmetic, without treating the external JSON or interval verifier as a Lean axiom."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sharp-error-ball"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilPrime3ProjectiveReadout.prime3_error_ball_iff"), H("Exact integer readout threshold"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the exact budget, uniform nonvanishing over the closed orthogonal error ball is equivalent to 15303 times the readout norm squared being less than 16510303 times the candidate overlap squared."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("capture-and-readouts"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaBridge/WeilPrime3ProjectiveReadout.prime3_capture_and_readouts"), H("Conditional full-domain certificate consumer"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under explicit genuine complex operator-domain symmetry, eigenvector and full complement-coercivity inputs, derives nonzero overlap, radius below 61/2000, centered errors for all readouts and nonzero actual eigenvector readouts under the integer margin. It does not supply the actual arithmetic Weil domain bridge or an increasing-scale estimate."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/Hankel/ProjectiveReadoutSharpness"))]));
}
