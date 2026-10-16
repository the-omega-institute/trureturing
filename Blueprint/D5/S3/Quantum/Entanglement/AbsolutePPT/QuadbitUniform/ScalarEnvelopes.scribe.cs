using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.QuadbitUniform;

internal sealed class ScalarEnvelopesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Natural integer bulk maximum.",
        H("Natural integer bulk maximum"), Blocks(
            Describe.Lean(DescribeId.Create("appt-quadbit-scalarenvelopes"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/QuadbitUniform/ScalarEnvelopes.bulk_integer_maximum"),
                H("Natural integer bulk maximum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N at least 67 and natural j, the bulk ratio (9N+16j)/(3N+2j)^2 is at " +
                    "most its value at natural t=(3N+4)/8. Boundary and middle ray inequalities are reduced to " +
                    "polynomial certificates. Their rational envelopes are bounded by a common envelope, which " +
                    "is below the integer bulk value after the exact rounding inequalities. Natural division " +
                    "takes place before coercion to the reals."))), DescribeRole.Theorem),
            Paragraph(Text("These statements concern real scalar spectra and finite cofactor certificates. Connecting " +
                    "the boundary inequalities to a physical APPT model, constructing an attaining state, and " +
                    "determining a purity supremum require additional results.")))));
}
