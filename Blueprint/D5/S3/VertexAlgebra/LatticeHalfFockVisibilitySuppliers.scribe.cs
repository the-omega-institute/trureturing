using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockVisibilitySuppliersDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original visibility suppliers",
        H("Exact original operations used by the repaired conformal route"),
        Blocks(Paragraph(Text("These public suppliers expose exact original oscillator and word-weight identities needed by the visible conformal application. They preserve the unrestricted original carrier and reuse predecessor mathematics; they do not introduce a replacement field or a bind-only mathematical endpoint.")),
            Describe.Lean(
                DescribeId.Create("latticehalffockvisibilitysuppliers-l-zero-x-mul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockVisibilitySuppliers.L_zero_X_mul"),
                H("Original L0 oscillator supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The L0 action on a creation generator is exposed with both inverse-Gram equations, preserving the exact Sugawara hypotheses."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticehalffockvisibilitysuppliers-word-weight-occurrences"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockVisibilitySuppliers.wordWeight_occurrences"),
                H("Original occurrence weight supplier"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("The occurrence word weight equals the Finsupp source-weight sum by the original finite occurrence construction."))),
                DescribeRole.Theorem))));
}
