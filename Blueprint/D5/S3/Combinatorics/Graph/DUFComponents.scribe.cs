using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph;

internal sealed class DUFComponentsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DUFComponents.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Let H be a finite family of subsets of a finite vertex type. The link and block definitions use its actual triples and apply to every such H. Under the cap of at most four neighbors per ground pair, a complete four-by-four block saturates every pair joining its center to its support. Its support is then a whole connected component of the center's link.",
        H("Reciprocal fibers and actual link components"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("link"),
                DeclarationHandle.Create(Prefix + "link"),
                H("Vertex links"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The simple graph L(c) has an edge xy precisely when x and y are distinct, both differ from c, and {c,x,y} belongs to H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("completeblock"),
                DeclarationHandle.Create(Prefix + "CompleteBlock"),
                H("Complete four-by-four configurations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A block consists of two disjoint four-element sets A and S, a center c outside both, and every triple {c,x,y} for x in A and y in S in H. This predicate refers only to actual triples."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("blocks"),
                DeclarationHandle.Create(Prefix + "blocks"),
                H("Counting by center and support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite block set contains pairs (c,U) with an eight-element support U admitting such a bipartition. The two sides and their ordering are existential witnesses, not counted objects."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("b"),
                DeclarationHandle.Create(Prefix + "B"),
                H("The center/support block count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("B(H) is the cardinality of the center/support block set for any H. Under the codegree cap of four, the component equivalence identifies it with the total number of connected K4,4 components in all vertex links, counted by center and support."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("reciprocal-four-fiber"),
                DeclarationHandle.Create(Prefix + "reciprocal_four_fiber"),
                H("Reciprocal four-star fibers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap, if S has four vertices and F(S) has four edges, there are a center c and a four-element leaf set A forming a complete block (c,A,S), with F(S)=cA and F(A)=cS. Every representation F(S)=dT with d outside T satisfies d=c and T=A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block-component"),
                DeclarationHandle.Create(Prefix + "block_component"),
                H("Saturation gives an entire component"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying the cap and a complete block (c,A,S), N({c,x})=S for every x in A and N({c,y})=A for every y in S. For every x in A union S and every ground vertex y, link adjacency holds exactly when x is in A and y is in S, or x is in S and y is in A. Thus there are no outgoing edges. Paths of length at most two connect A union S, which equals the support of an actual connected component of L(c)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("blocks-iff-component"),
                DeclarationHandle.Create(Prefix + "blocks_iff_component"),
                H("Exact component semantics"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying the cap, (c,U) belongs to the block set if and only if U is the support of a connected component of L(c) admitting disjoint four-element parts A and S with U=A union S and the following adjacency: for every x in U and every ground vertex y, xy is an edge exactly when x is in A and y is in S, or x is in S and y is in A. The reverse direction recovers the actual triples and excludes c from U."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("block-fibers"),
                DeclarationHandle.Create(Prefix + "block_fibers"),
                H("Both fibers of a complete block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For H satisfying DUF and the cap and every complete block (c,A,S) in H, F(S)=cA and F(A)=cS. The cap saturates neighborhoods, while the intersecting-family bound excludes additional fiber edges."))),
                DescribeRole.Theorem)),
        []));
}
