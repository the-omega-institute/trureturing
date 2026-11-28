using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.DeletionResilientCliques;

internal sealed class EdgeBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/DeletionResilientCliques/EdgeBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Appendix A gives an edge threshold for deletion-resilient graphs without a large clique.",
        H("The nonclique edge bound"),
        Blocks(
            Describe.Lean(DescribeId.Create("nonclique-edge-bound"),
                DeclarationHandle.Create(Prefix + "nonclique_edge_bound"),
                H("The nonclique edge bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Hamming/liuzhangyuzhangji2026optimalcpecc")),
                Blocks(Paragraph(Text("Let t ≥ 1 and w > t + 3. Suppose a finite graph has at least w + t vertices, minimum degree at least w − 1, and no clique of order w + t. If deletion of any t vertices leaves a w-clique, its number of edges is at least B(w,t), the sum of the two binomial coefficients choosing 2 from w + floor((t − 1)/2) and from w + floor(t/2). The critical-cover bound for the complement forces at least 2w + t − 1 vertices. The colorable induced subgraph estimate bounds the reciprocal-degree sum. Cauchy–Schwarz and the degree sum then give an edge bound increasing from order 2w + t − 1, where it rounds up to B(w,t)."))), DescribeRole.Theorem)),
        []));
}
