using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class CompatibleLowerCoverFenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An obstruction to compatible categorical homotopies",
        H("An obstruction to compatible categorical homotopies"),
        Blocks(Describe.Lean(
            DescribeId.Create("regional-contractions-disagree-on-a-shared-singleton"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/CompatibleLowerCoverFence.exists_disjoint_singleton_of_schedule"),
            H("A noncontractible face poset forces disjoint images of a shared singleton"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(Paragraph(Text("Suppose two lower sets cover a face poset that admits no contraction. At each stage of the two regional homotopies, the regional maps may change in either order direction independently. The homotopies start at the inclusions and use a common constant endpoint or take place in a connected ambient face poset. Some stage must send a shared singleton to disjoint faces. Otherwise the regional maps glue by taking their intersection on the overlap, and taking the larger map independently on each side inserts a compatible common upper stage between consecutive pairs. The assembled homotopy would contract the ambient face poset."))),
            DescribeRole.Theorem))));
}
