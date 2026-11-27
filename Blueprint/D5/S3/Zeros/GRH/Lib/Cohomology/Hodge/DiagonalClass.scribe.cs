using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Hodge;

internal sealed class DiagonalClassDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal Class", H("Diagonal Class"),
        Blocks(
            Paragraph(Text("Class of the diagonal in Hodge cohomology, glued from local Grothendieck symbols.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Hodge/DiagonalClass.exists_diagonal_class"),
                H("exists_diagonal_class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Class of the diagonal: if X has an atlas of dimension d, some δ in Hdg^d(X × X, complement of the diagonal) is, near each diagonal field point, the symbol [df/f], where f_i = x_i ⊗ 1 − 1 ⊗ x_i for chart coordinates x cut out the diagonal.")))))));
}
