using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Witt;

internal sealed class SpaceOperationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Space Operations", H("Space Operations"),
        Blocks(
            Paragraph(Text("Witt's extension theorem for primitive frames over integral finite adeles, unramified CM case. Unimodular hermitian forms over integral adeles have orthonormal bases; real units are norms. Orthogonal sums, negatives, reindexing, moving of framed hermitian spaces and their adelic groups.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Witt/SpaceOperations.star_normNegOne_mul_self"),
                H("star_normNegOne_mul_self"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For stably unramified E, the chosen unit ε = Weil.normNegOne of Ô satisfies ε̄ε = −1 in the finite adeles of E.")))))));
}
