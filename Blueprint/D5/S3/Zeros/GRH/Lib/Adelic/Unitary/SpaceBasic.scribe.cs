using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Unitary;

internal sealed class SpaceBasicDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Space Basic", H("Space Basic"),
        Blocks(
            Paragraph(Text("Basic API for rational points, block embeddings and vectors of framed hermitian spaces.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceBasic.witt"),
                H("witt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Witt's theorem for a hermitian space V: if X, Y are left invertible n × m matrices over E with XᴴJX = YᴴJY, J the matrix of V, then gX = Y for some g in U(J)(E).")))))));
}
