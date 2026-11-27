using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Adelic.Reduction;

internal sealed class FirstMinimumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "First Minimum", H("First Minimum"),
        Blocks(
            Paragraph(Text("First minimum of hermitian lattices: positivity, comparison, short vectors are orthogonal.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Adelic/Reduction/FirstMinimum.firstMinimum_pos"),
                H("firstMinimum_pos"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For every space V, λ > 0, where λ is the first minimum of the lattice of V cut off at 1 (Space.firstMinimum).")))))));
}
