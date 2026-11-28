using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StableCategory;

internal sealed class TetrahedralCategoricalCoverDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A two-piece stable categorical cover in dimension three",
        H("A two-piece stable categorical cover in dimension three"),
        Blocks(Describe.Lean(
            DescribeId.Create("relative-two-piece-cover"),
            DeclarationHandle.Create("D5/S3/Topology/StableCategory/TetrahedralCategoricalCover.two_meeting_face_pieces_of_rank"),
            H("A relative two-piece cover by face neighborhoods"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Topology/mosqueraloistanaka2026stablecategory")),
            Blocks(
                Paragraph(Text("Let a nonempty finite subcomplex have a proper four-rank coloring and a nullhomotopic realization inclusion in a finite ambient complex with connected one-skeleton. At a common ordinary subdivision depth, it admits a cover by two subcomplexes whose maps into the subdivided ambient lie in the contiguity class of constants.")),
                Paragraph(Text("The nullhomotopy restricts to both rank graphs. The tetrahedral refinement gives two categorical induced regions. In one further subdivision, intersecting each face with the selected region gives a face map below the ambient inclusion. Every flag belongs to the neighborhood selected by a vertex of its least face."))),
            DescribeRole.Theorem), Describe.Lean(
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
