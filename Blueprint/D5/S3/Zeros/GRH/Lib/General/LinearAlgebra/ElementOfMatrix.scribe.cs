using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class ElementOfMatrixDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Element Of Matrix", H("Element Of Matrix"),
        Blocks(
            Paragraph(Text("The element of an adelic unitary group with a given isometric matrix.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ElementOfMatrix.ofMat"),
                H("ofMat"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The element of the adelic unitary group of signs s given by an adelic matrix m with m*εm = ε, ε the standard form.")))))));
}
