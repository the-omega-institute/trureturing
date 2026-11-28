using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class CategoricalCoverFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Categorical covers from factored inclusions",
        H("Categorical covers from factored inclusions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("categorical-cover-of-factorizations"),
                DeclarationHandle.Create("D5/S3/Topology/StableCategory/CategoricalCoverFactorization.hasCategoricalCover_of_factorizations"),
                H("A lower cover through categorical-cover factors"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
                Blocks(Paragraph(Text("Suppose a poset is covered by a family of a lower sets, each with an inclusion that factors through a poset covered by b categorical lower sets. Pull back each of those sets to its region and compose its contraction into the ambient poset. This gives a categorical lower cover by a times b sets."))),
                DescribeRole.Theorem))));
}
