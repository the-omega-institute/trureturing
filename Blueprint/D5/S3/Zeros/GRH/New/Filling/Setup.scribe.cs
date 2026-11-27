using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Filling;

internal sealed class SetupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Setup", H("Setup"),
        Blocks(
            Paragraph(Text("Data record for filling, size hypotheses, names for groups, terms, amplitudes and constants.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Filling/Setup.exists_cutoff_classUnip"),
                H("exists_cutoff_classUnip"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("The image of a subgroup K of 𝖴_c(g) at the infinite places is discrete and has a cutoff: a measurable β with values in [0, ∞] and ∑_{u∈K} β(uy) = 1 for all y.")))))));
}
