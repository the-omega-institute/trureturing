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
            Describe.Lean(DescribeId.Create("complete-central-parity-band"),
                DeclarationHandle.Create(Prefix + "Band"),
                H("Labelled narrow-band spaces"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Band n c lab is the point set {0,…,n−1} where a pair i<j with label "
                    + "r=lab(i,j)<c is at distance 1+r/(2(n+c)) and every other pair gets its own "
                    + "distance 3/2+(in+j)/(2n²). All distances of distinct points lie in [1,2), "
                    + "so the triangle inequality holds. If every label below c occurs at every "
                    + "point and a pair with a larger label always leaves a third point, the "
                    + "central values are exactly 0 and 1+r/(2(n+c)) for r<c: a value used by "
                    + "one pair only is missed at the third point. Central neighbours are then "
                    + "the pairs with label below c. This is the realization step (eq. "
                    + "realization) of H. Ma and W. Zhang, who note that it uses the narrow-band "
                    + "metric principle of O. Dovgoshey and O. Rovenska (proof of Theorem 3.8, "
                    + "formula (19))."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("complete-central-parity-space"),
                DeclarationHandle.Create(Prefix + "Space"),
                H("The round-robin space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Space m is the band on 2m+2 points whose labels are round-robin classes. "
                    + "With M=2m+1 and the point M playing the role of ∞, a pair {i,j} of points "
                    + "below M lies in class (i+j) mod M and a pair {i,∞} in class 2i mod M; this "
                    + "is the round-robin one-factorization of the complete graph on 2m+2 points "
                    + "into M perfect matchings (the 1-factorability of K_2n, F. Harary, Graph "
                    + "Theory, 1969). All M classes are central."))),
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
                    + "works. For even n=2m+2 every class is a perfect matching, so each of the "
                    + "2m+1 class distances is central; together with 0 these are the 2m+2 "
                    + "central values, and every pair of distinct points is at a central "
                    + "distance. This is Theorem 5 of H. Ma and W. Zhang."))),
                DescribeRole.Theorem))));
}
