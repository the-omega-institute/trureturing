using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class LeadingRayCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Leading support ray certificates.",
        H("Leading support ray certificates"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-leadingraycertificates"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/LeadingRayCertificates.leadingRayCertificates"),
                H("Leading support ray certificates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original identifiers 29 through 91 have three nonzero gaps, with least supported slot " +
                    "strictly before the middle slot. For every identifier the nonnegative coefficients, " +
                    "positive reference mass, exact linear and Gram moments, and boundary or middle branch " +
                    "inequality are proved with the supplied arithmetic certificates."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
