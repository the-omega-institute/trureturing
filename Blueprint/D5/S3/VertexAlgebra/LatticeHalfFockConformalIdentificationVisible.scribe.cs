using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeHalfFockConformalIdentificationVisibleDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Visible original conformal identification",
        H("The exact original Ytw omega application"),
        Blocks(Describe.Lean(
            DescribeId.Create("latticehalffockconformalidentificationvisible-ytw-omega"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockConformalIdentificationVisible.Ytw_omega"),
            H("Visible original conformal identification"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Background),
            Blocks(Paragraph(Text("The public compatibility suppliers reproduce the protected tensor-pair finiteness, pair ordering and inverse-trace identities, then apply the original Leech carrier and both inverse hypotheses. The predecessor private declarations remain untouched; this module repairs visibility rather than changing the conformal statement."))),
            DescribeRole.Theorem))));
}
