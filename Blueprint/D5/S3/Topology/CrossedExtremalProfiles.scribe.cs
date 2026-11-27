using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class CrossedExtremalProfilesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers for the crossed extremal incidence",
        H("Categorical covers for the crossed extremal incidence"),
        Blocks(Describe.Lean(
            DescribeId.Create("crossed-incidence-two-cover"),
            DeclarationHandle.Create(
                "D5/S3/Topology/CrossedExtremalProfiles.hasCategoricalCover_double_subdivision"),
            H("Two categorical open sets cover the second subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text(
                "The minimal points pair the four intermediate vertices twice, and the maximal points give the complementary four-cycle. " +
                "Two explicit fences contract the pieces of a vertex partition into the ambient poset. " +
                "The subdivision transfer makes this partition a categorical open cover."))),
            DescribeRole.Theorem))));
}
