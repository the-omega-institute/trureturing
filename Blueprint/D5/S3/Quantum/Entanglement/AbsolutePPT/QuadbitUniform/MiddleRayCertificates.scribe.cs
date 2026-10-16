using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class MiddleRayCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Middle gap ray certificates.",
        H("Middle gap ray certificates"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-middleraycertificates"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/MiddleRayCertificates.middleRayCertificates"),
                H("Middle gap ray certificates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original identifiers 142 through 186 have four nonzero gaps and positive gap at the middle " +
                    "slot. Their exact moments and middle-envelope inequalities hold with nonnegative " +
                    "coefficients and positive reference mass. The final identifier retains the original " +
                    "default branch of the ray table."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
