using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GraphSubstitution;

internal sealed class IndependenceFibersDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GraphSubstitution/IndependenceFibers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent supports and fibers describe heterogeneous graph substitution.",
        H("Independence in heterogeneous graph substitution"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("heterogeneous-graph-substitution"),
                DeclarationHandle.Create(Prefix + "substitution"),
                H("The actual substituted graph"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let B be any simple graph on V, let W assign a vertex type to every base vertex, and let H(i) be a simple graph on W(i). The vertices of the substituted graph are dependent pairs (i,a). Two pairs are adjacent exactly when their base vertices are adjacent in B, or when they belong to the same fiber and their fiber vertices are adjacent in H(i). Thus every base edge completely joins the two corresponding fibers, while every internal fiber graph is retained. Empty fibers and infinite vertex types are allowed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("substitution-occupied-support"),
                DeclarationHandle.Create(Prefix + "support"),
                H("Occupied base vertices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a set T of dependent pairs, support T is its image under the first-coordinate projection. A base vertex is in this support exactly when T contains at least one actual vertex in its fiber."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("substitution-selected-fiber"),
                DeclarationHandle.Create(Prefix + "fiber"),
                H("Selected vertices of a fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The selected fiber at i is the preimage of T under a ↦ (i,a). Unoccupied fibers give empty selected sets. Independence is meaningful for these empty sets as well."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("substitution-independent-support-fibers"),
                DeclarationHandle.Create(Prefix + "isIndepSet_substitution_iff"),
                H("Exact support and fiber decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every base graph B, every dependent family W and fiber graphs H, and every set T of substituted vertices, T is independent in the actual substituted graph if and only if its support is independent in B and every selected fiber is independent in its own H(i). This statement has no finiteness, decidable-equality, or inhabited-fiber assumptions. In the forward direction, witnesses above two occupied base vertices rule out a base edge, and pairs in a single fiber rule out an internal edge. In the reverse direction, either kind of an actual substitution edge contradicts the corresponding independence condition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("graph-independence-complex"),
                DeclarationHandle.Create(Prefix + "independenceComplex"),
                H("The independence complex and its nonempty faces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any simple graph G, the independence complex is the Mathlib abstract simplicial complex whose faces are exactly the nonempty finite independent sets of G. Every singleton is a face. Nonempty subsets preserve independence, giving the downward-closure proof."))),
                DescribeRole.Definition),
            Paragraph(Text("Applying the support-and-fiber theorem to a finite set σ gives the exact face criterion for the independence complex of the substituted graph: σ is nonempty, its occupied base support is independent, and each selected fiber is independent. Equivalently, the nonempty selected fibers are faces of their fiber independence complexes. An empty selected fiber must remain allowed, since Mathlib complexes omit the empty face. This is an application of the set theorem and the complex definition.")),
            Paragraph(Text("This provides the combinatorial entry point for substitution arguments on independence complexes. A later link calculation at an actual fiber vertex must retain the other nonneighbors inside that fiber. Deleting the entire occupied base fiber is justified in the singleton-fiber case used when a base vertex has not yet been replaced. Topological realization, collapses, and homotopy decompositions require further proofs."))
        )));
}
