using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFSeparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFSeparation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of an n-element vertex type. Under DUF, complete blocks with different centers have at most one vertex in each side-intersection cell, and the four cells cannot all be occupied. Under the additional cap of at most four neighbors per ground pair, these blocks are whole link components and satisfy the center and component separation bounds. Three-uniformity is assumed only for the final counting bound.",
        H("Fifteen-vertex separation and the fourteen-vertex bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("block-cell-bound"),
                DeclarationHandle.Create(Prefix + "block_cell_bound"),
                H("At most one vertex per intersection cell"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, A and C intersect in at most one vertex. Two shared vertices would place two large stars with different centers in one common link, where disjoint edges can be selected, contradicting DUF."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block-support-overlap"),
                DeclarationHandle.Create(Prefix + "block_support_overlap"),
                H("At most three shared leaves"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, the supports A union S and C union D overlap in at most three vertices. Four nonempty side-intersection cells would give two disjoint diagonal edges in the common link of the centers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block-center-overlap"),
                DeclarationHandle.Create(Prefix + "block_center_overlap"),
                H("Centers cannot enter in both directions"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap and complete blocks (c,A,S) and (d,C,D) in H with c distinct from d, if d belongs to A union S, then c does not belong to C union D and the two supports share at most two vertices. Saturation identifies opposite neighborhoods and excludes an entire side from the other component."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("components-separated"),
                DeclarationHandle.Create(Prefix + "components_separated"),
                H("The separation bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap, take two distinct members (c,U) and (d,W) of the center/support block set. The union of U with c included and W with d included has at least fifteen vertices. If c=d, the two component supports are disjoint and this union has exactly seventeen vertices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fourteen-vertex-bound"),
                DeclarationHandle.Create(Prefix + "fourteen_vertex_bound"),
                H("At most fourteen vertices"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite vertex type of size at most fourteen and every actual three-uniform DUF family H with maximum pair codegree at most four, card(H)<=binom(n,2). Separation permits at most one exceptional component, and the exact counting identity then gives the bound. This is a restricted consequence, not a solution of the unrestricted problem."))),
                DescribeRole.Theorem)),
        []));
}
