using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class TetrahedralCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-piece stable categorical cover in dimension three",
        H("A two-piece stable categorical cover in dimension three"),
        Blocks(Describe.Lean(
            DescribeId.Create("contractible-order-complex-two-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_lower_sets_of_contractible_order_complex"),
            H("Two categorical lower sets after ordinary subdivision"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("Let a finite poset have order-complex dimension at most three. An actual contraction of its order-complex realization gives a cover by two categorical lower sets after finitely many ordinary subdivisions.")),
                Paragraph(Text("The heights of the poset elements give four ranks. Pairing ranks gives two bipartite graphs. Repeated tetrahedral refinements subdivide each parameter graph four times for every three ambient subdivisions. Fixed-target graph contractions then apply through the original edge carriers, and the face-meeting construction transfers the two induced regions to lower sets."))),
            DescribeRole.Theorem))));
}
