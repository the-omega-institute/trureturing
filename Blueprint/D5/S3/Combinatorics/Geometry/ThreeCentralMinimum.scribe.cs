using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class ThreeCentralMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/ThreeCentralMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every n ≥ 4 the least number of central edges of a three-central n-point metric "
            + "space is 2⌈n/2⌉.",
        H("The sharp three-central minimum"),
        Blocks(
            Describe.Lean(DescribeId.Create("three-central-minimum-space"),
                DeclarationHandle.Create(Prefix + "Space"),
                H("The narrow-band space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Space N is the point set {0,…,n−1} with n=N+4. The pairs {2k,2k+1} "
                    + "(closed by {0,n−1} when n is odd) are at distance 1; the pairs {2k+1,2k+2} "
                    + "(closed by {0,n−1} when n is even and by {0,2} when n is odd) are at "
                    + "distance 2; each of these two classes has ⌈n/2⌉ pairs and covers every "
                    + "point, and the classes are disjoint. Every other pair {i,j} with i<j is at "
                    + "distance 1+(n·i+j+1)/(n²+1), a value strictly between 1 and 2 that no other "
                    + "pair takes. All nonzero distances lie in [1,2], so the triangle inequality "
                    + "holds."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("three-central-minimum-result"),
                DeclarationHandle.Create(Prefix + "three_central_minimum"),
                H("The minimum is 2⌈n/2⌉"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every n ≥ 4, every three-central metric space on n points has at least "
                    + "2⌈n/2⌉ central edges, and the narrow-band space attains 2⌈n/2⌉. The lower "
                    + "bound is the edge-cover bound with k=3. In the narrow-band space 0, 1 and 2 "
                    + "are central. Any other central value t is the distance of a single pair, "
                    + "since distances outside the two classes determine their pair; a third "
                    + "point would then have no partner at distance t. So the center is {0,1,2}, "
                    + "the central edges are exactly the two classes, and there are at most "
                    + "2⌈n/2⌉ of them. This is Theorem 3 of H. Ma and W. Zhang."))),
                DescribeRole.Theorem))));
}
