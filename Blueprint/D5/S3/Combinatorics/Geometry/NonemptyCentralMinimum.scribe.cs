using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class NonemptyCentralMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/NonemptyCentralMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonempty central graph on n ≥ 2 points has at least ⌈n/2⌉ edges, with equality "
            + "exactly for the bicentral perfect matchings and their odd analogues.",
        H("Minimum nonempty central graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("nonempty-central-minimum-degrees"),
                DeclarationHandle.Create(Prefix + "EqualityDegrees"),
                H("The equality degrees"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "A graph on n points has the equality degrees when every degree is 1 and n "
                    + "is even, or when n is odd, one point has degree 2 and every other point "
                    + "has degree 1. These are the graphs (n/2)P₂ and P₃ ∪ ((n−3)/2)P₂: the two "
                    + "neighbours of the degree-2 point have degree 1, so they form a path on "
                    + "three points, and the rest is a perfect matching."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("nonempty-central-minimum-result"),
                DeclarationHandle.Create(Prefix + "nonempty_minimum"),
                H("The nonempty minimum and its equality graphs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n ≥ 2 the least number of edges of a nonempty central graph on n points "
                    + "is ⌈n/2⌉. One central edge of length t makes t central, so every point has "
                    + "a central neighbour and there are at least two central values; the "
                    + "edge-cover bound then gives ⌈n/2⌉ edges, and a bicentral space attains it. "
                    + "At equality the edge-cover bound forces exactly two central values, and "
                    + "the degrees, all at least 1, add up to 2⌈n/2⌉, which is n or n+1; so they "
                    + "are the equality degrees. Conversely, the band whose central pairs are "
                    + "the edges of such a graph realizes it as a central graph. Without the "
                    + "nonemptiness condition the minimum is 0 for n ≥ 3, by a one-central "
                    + "space. This is Corollary 8 of H. Ma and W. Zhang; the nonempty minimum is "
                    + "Theorem 3.10 of O. Dovgoshey and O. Rovenska, whose Theorem 3.12 printed "
                    + "the odd equality graph as P₃ ∪ hP₂ for n=2h+1 instead of P₃ ∪ (h−1)P₂."))),
                DescribeRole.Theorem))));
}
