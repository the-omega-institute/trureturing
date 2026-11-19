using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class CompleteCentralParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/CompleteCentralParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An n-point metric space with n central distances and a complete central graph exists "
            + "exactly when n=1 or n is even.",
        H("Parity of complete n-central metric graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("complete-central-parity-space"),
                DeclarationHandle.Create(Prefix + "Space"),
                H("The round-robin space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Space m is the point set {0,…,2m+1}. With M=2m+1 and the point M playing "
                    + "the role of ∞, a pair {i,j} of points below M lies in class (i+j) mod M and "
                    + "a pair {i,∞} in class 2i mod M; this is the round-robin one-factorization "
                    + "of the complete graph on 2m+2 points into M perfect matchings (the "
                    + "1-factorability of K_2n, F. Harary, Graph Theory, 1969). Distinct points in "
                    + "class r are at distance 1+r/(2m+2), a value in [1,2), so the triangle "
                    + "inequality holds."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-central-parity-result"),
                DeclarationHandle.Create(Prefix + "complete_central_iff"),
                H("The parity classification"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n ≥ 1, some metric space on n points has exactly n central distances "
                    + "and a complete central graph if and only if n=1 or n is even. For odd "
                    + "n=2k+1 ≥ 3 the edge-cover bound gives at least (n−1)(k+1)=2k(k+1) central "
                    + "edges, more than the k(2k+1) pairs available. For n=1 a single point "
                    + "works. For even n=2m+2 every class is a perfect matching, so each value "
                    + "1+r/(2m+2) with r<2m+1 is central; together with 0 these are the 2m+2 "
                    + "central values, and every pair of distinct points is at a central "
                    + "distance. This is Theorem 5 of H. Ma and W. Zhang."))),
                DescribeRole.Theorem))));
}
