using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Cohomology.Etale;

internal sealed class FilteredColimitsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Filtered Colimits", H("Filtered Colimits"),
        Blocks(
            Paragraph(Text("Commutation of cohomology with filtered limits descends along Čech covers.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Cohomology/Etale/FilteredColimits.of_cech"),
                H("of_cech"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Take a cone over a cofiltered system of covers E_j → Y_j whose vertex is a cover. If ContinuousUpTo holds at level r+1 for the E_j and at level r for all fibre powers with at least one factor, it holds at level r+1 for the Y_j.")))))));
}
