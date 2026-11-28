using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class FillingAdmissibleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Filling Admissible", H("Filling Admissible"),
        Blocks(
            Paragraph(Text("Index and class counts of columns; the filling data are admissible.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/FillingAdmissible.relIndex_latStabilizer"),
                H("relIndex_latStabilizer"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The elements of the stabiliser of the standard lattice of X₀ that preserve the lattice of Y₀ have index (N^k − 1)^f.")))))));
}
