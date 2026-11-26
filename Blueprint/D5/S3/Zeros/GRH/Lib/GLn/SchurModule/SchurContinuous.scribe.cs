using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.GLn.SchurModule;

internal sealed class SchurContinuousDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schur Continuous", H("Schur Continuous"),
        Blocks(
            Paragraph(Text("Continuity of the Schur matrix in its argument.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/GLn/SchurModule/SchurContinuous.continuous_schur"),
                H("continuous_schur"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Over a topological commutative ring R, the map sending a tuple g of square matrices to its Schur matrix S_κ(g) is continuous.")))))));
}
