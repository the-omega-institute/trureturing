using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Unitary;

internal sealed class SpaceGramDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Space Gram", H("Space Gram"),
        Blocks(
            Paragraph(Text("Gram matrix of an adelically framed hermitian space is invertible and hermitian.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Unitary/SpaceGram.isHermitian_J"),
                H("isHermitian_J"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The matrix J over E of a space (J, x) is hermitian: Jᴴ = J.")))))));
}
