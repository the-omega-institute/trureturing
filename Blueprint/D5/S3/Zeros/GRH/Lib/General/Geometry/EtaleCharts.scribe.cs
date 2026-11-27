using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.Geometry;

internal sealed class EtaleChartsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Etale Charts", H("Etale Charts"),
        Blocks(
            Paragraph(Text("Charts with étale coordinates on functors: lifting criterion, shrinking, products, intersections, atlases.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/Geometry/EtaleCharts.exists_isCharting"),
                H("exists_isCharting"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If X has an atlas of dimension d, there is a subfunctor V of X satisfying IsCharting.")))))));
}
