using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Laman;

internal sealed class SparseSetsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Laman/SparseSets.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/chen2026combinatorialrigidity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite simple graph counts, tight subsets, and exact Henneberg operations over arbitrary vertex types.",
        H("Sparsity and tight-set closure"), Blocks(
            Describe.Lean(DescribeId.Create("sparsesets-0"), DeclarationHandle.Create(Prefix + "edgesIn"),
                H("Edges induced by a vertex set"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every vertex type V, graph G and set S of vertices, edgesIn G S consists of the actual edges of G whose two endpoints lie in S. The map induced by subtype inclusion identifies it bijectively with the edge set of G induced on S."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsesets-1"), DeclarationHandle.Create(Prefix + "IsSparse"),
                H("Additive sparsity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every graph G and natural numbers k and ell, sparsity requires e(s)+ell <= k card(s) for every finite vertex set s for which ell <= k card(s). The additive convention avoids truncated natural subtraction."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsesets-2"), DeclarationHandle.Create(Prefix + "IsTight"),
                H("Global tightness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every graph G and natural k and ell, tightness combines sparsity with card(E(G))+ell=k card(V). Nat.card allows a universe-polymorphic statement; the constructions use finite V."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsesets-3"), DeclarationHandle.Create(Prefix + "IsTightOn"),
                H("Local tightness"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every graph G, natural k and ell and finite vertex set s, local tightness is the equality e(s)+ell=k card(s)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("sparsesets-4"), DeclarationHandle.Create(Prefix + "exists_one_le_degree_le_three"),
                H("A positive low-degree vertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For every finite graph G that is (2,3)-sparse and has an edge, some vertex has degree between one and three. Restrict the degree sum to the vertices of positive degree. Every edge has both endpoints there. If all their degrees were at least four, handshake and sparsity on that same set would contradict each other."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparsesets-5"), DeclarationHandle.Create(Prefix + "exists_nonadj_among_three_neighbors"),
                H("A nonadjacent neighbor pair"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("In a finite (2,3)-sparse graph, three distinct neighbors of any vertex cannot all be mutually adjacent. The four-vertex induced set would have six edges, exceeding its permitted five."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparsesets-6"), DeclarationHandle.Create(Prefix + "union_inter"),
                H("Union and intersection of tight sets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary k and ell and two tight finite sets s and t in a finite sparse graph, if ell <= k card(s intersection t), both the union and intersection are tight. Supermodularity of actual induced-edge counts and the cardinality identity squeeze the two sparsity inequalities simultaneously."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparsesets-7"), DeclarationHandle.Create(Prefix + "union_with_bonus"),
                H("Tight union with extra edges"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary k and ell and a finite (k,ell)-sparse graph G, tight sets S and T have tight union if a set F of actual edges in their union is disjoint from the edges internal to S or T and its size closes the intersection deficit: e(S intersection T)+ell <= card(F)+k card(S intersection T). The proof counts the disjoint extra edges before applying sparsity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sparsesets-8"), DeclarationHandle.Create(Prefix + "insert_vertex_with_edges"),
                H("Tight extension by one vertex"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary sparse G and tight finite S, let w lie outside S. If F consists of actual edges in S union {w}, disjoint from the edges internal to S, and k <= card(F), then S union {w} is tight. The edge-count lower bound and sparsity upper bound coincide."))), DescribeRole.Theorem)), []));
}
