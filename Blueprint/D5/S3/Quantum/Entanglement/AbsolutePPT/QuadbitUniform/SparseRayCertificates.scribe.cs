using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class SparseRayCertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse original ray certificates.",
        H("Sparse original ray certificates"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-sparseraycertificates"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/SparseRayCertificates.sparseRayCertificates"),
                H("Sparse original ray certificates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Original identifiers 0 through 28 have sparse one- or two-coordinate gap patterns. Each " +
                    "supplied proof establishes nonnegative mass coefficients, strictly positive reference " +
                    "mass, all six exact moments, and the applicable branch inequality. Their original order " +
                    "and all sixteen coordinates are retained."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
