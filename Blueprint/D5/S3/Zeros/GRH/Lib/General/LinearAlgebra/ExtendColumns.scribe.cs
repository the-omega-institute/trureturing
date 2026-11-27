using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.LinearAlgebra;

internal sealed class ExtendColumnsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extend Columns", H("Extend Columns"),
        Blocks(
            Paragraph(Text("Kronecker products, parabolic, unitriangular, Levi, parahoric subgroups; Bessel subgroups and frame of the space. Independent columns extend to an invertible matrix; standard inclusion is injective.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/LinearAlgebra/ExtendColumns.exists_GL_mul_inclMatrix"),
                H("exists_GL_mul_inclMatrix"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("A matrix b over a field with linearly independent columns extends to an invertible matrix u: column ι(j) of u is column j of b.")))))));
}
