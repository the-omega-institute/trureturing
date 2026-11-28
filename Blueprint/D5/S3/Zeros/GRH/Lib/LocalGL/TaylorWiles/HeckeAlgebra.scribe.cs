using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.LocalGL.TaylorWiles;

internal sealed class HeckeAlgebraDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hecke Algebra", H("Hecke Algebra"),
        Blocks(
            Paragraph(Text("Algebra of scalar systems preserving integral forms, its action and closedness.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/LocalGL/TaylorWiles/HeckeAlgebra.isClosed_heckeAlgebra"),
                H("isClosed_heckeAlgebra"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The Hecke algebra is closed in the space of Q̄_ℓ-valued functions on systems.")))))));
}
