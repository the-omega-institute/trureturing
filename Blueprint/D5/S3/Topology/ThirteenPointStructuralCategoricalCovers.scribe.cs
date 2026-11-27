using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class ThirteenPointStructuralCategoricalCoversDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Thirteen-point categorical covers under added extremal comparisons",
        H("Thirteen-point categorical covers under added extremal comparisons"),
        Blocks(Describe.Lean(
            DescribeId.Create("thirteen-point-extremal-cover"),
            DeclarationHandle.Create(
                "D5/S3/Topology/ThirteenPointStructuralCategoricalCovers.cover_of_structural_table"),
            H("Categorical partitions persist under added extremal comparisons"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "Each of the 72 partitions separates minima from maxima. Adding only " +
                "comparisons from minima to maxima preserves both induced orders and " +
                "every inequality in their contractions. The resulting partitions give " +
                "categorical lower covers after two ordinary subdivisions."))),
            DescribeRole.Theorem))));
}
