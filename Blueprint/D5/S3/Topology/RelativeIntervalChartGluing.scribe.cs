using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class RelativeIntervalChartGluingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gluing relative interval contiguities",
        H("Gluing relative interval contiguities"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-contiguity-through-interval-charts"),
            DeclarationHandle.Create(
                "D5/S3/Topology/RelativeIntervalChartGluing.relative_contiguity_of_interval_charts"),
            H("Interpret a relative interval homotopy through facewise charts"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Assume every face has a common interval chart for the allowed positions of its " +
                "vertices. At a fixed vertex a chart need only agree at the fixed position. " +
                "A relative contiguity chain in the interval then gives a relative contiguity " +
                "chain in the target complex."))),
            DescribeRole.Theorem))));
}
