using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CompleteSubdivisionDegreeCollisionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Walks/CompleteSubdivisionDegreeCollision.";

    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/GraphInvariants/farhan2026multiset");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Repeated augmented degrees force collisions",
        H("Repeated augmented degrees force collisions"),
        Blocks(
            Paragraph(Text("A resolving set would force distinct augmented selected degrees. Equal original bits give a collision between reverse incidences. With unequal original bits, cancel the shared midpoint by swapping the two indices in a row sum; a strict comparison at an outside index supplies two distinct incidences with equal four-bin counts. The cancellation excludes both distinguished indices.")),
            Describe.Lean(DescribeId.Create("complete-subdivision-degree-collision-resolving-augmented-injective"),
                DeclarationHandle.Create(Prefix + "resolving_augmented_injective"),
                H("resolving augmented injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Resolution would make the selected midpoint degree plus original bit injective on all original vertices."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("complete-subdivision-degree-collision-resolving-rows-injective"),
                DeclarationHandle.Create(Prefix + "resolving_rows_injective"),
                H("resolving rows injective"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Consequently a resolving selection matrix would have pairwise distinct row sums."))), DescribeRole.Theorem))));
}
