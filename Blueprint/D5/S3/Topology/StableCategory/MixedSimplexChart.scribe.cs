using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class MixedSimplexChartDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two full regions in the subdivision of a simplex",
        H("Two full regions in the subdivision of a simplex"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mixed-block-cover"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/MixedSimplexChart.mixed_block_cover"),
                H("Two regions from disjoint vertex blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("A forbidden image requires a nonempty face in its own vertex block. Disjoint blocks give incomparable faces, which cannot both occur in the same chain. Their two pullbacks therefore cover the second ordinary barycentric subdivision."))),
                DescribeRole.Theorem))));
}
