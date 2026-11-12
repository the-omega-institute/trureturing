using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroDivisor;

internal sealed class NineRestrictionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/ZeroDivisor/NineRestriction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Restriction of marked-prefix and unmarked-pair counts to nine-element subsets.",
        H("Nine-element restriction"),
        Blocks(
            Describe.Lean(DescribeId.Create("nine-restriction-count"),
                DeclarationHandle.Create(Prefix + "nine_restriction_count"),
                H("Counting extensions of a selected prefix and pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary natural block sizes m and n and rank k between three and five, sum over j from zero through nine the product choose(m,j) choose(n,9-j) choose(j,k-1) choose(9-j,2). This equals choose(m,k-1) choose(n,2) choose(m+n-(k+1),9-(k+1)). All subtractions here are natural subtractions, and binomial coefficients vanish outside their natural support.")),
                    Paragraph(Text("Only k-1 through seven can contribute. Shifting by k-1 and applying the composed-choice identity in each block leaves Vandermonde convolution on the remaining elements. If either block cannot supply its selected elements, both sides vanish. This counts extensions in arbitrary populations, rather than only a population of size nine."))),
                DescribeRole.Theorem))));
}
