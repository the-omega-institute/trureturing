using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceConsecutiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceConsecutive.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 2143 endpoint classes are counted by shuffles and independent interval splits.",
        H("RotationAvoidanceConsecutive"),
        Blocks(
            Node("rotationavoidanceconsecutive-consecutive-shuffle-endpoint-count", "Consecutive endpoints and a binomial count", "consecutive_shuffle_endpoint_count", "For positive lowerCount and upperCount, permutations of one through lowerCount plus upperCount plus two beginning with lowerCount plus one and ending with lowerCount plus two, and containing 2143 in exactly the uncut rotation, number the binomial coefficient choosing lowerCount from lowerCount plus upperCount, minus one. Their interiors shuffle two increasing intervals; the ordered concatenation is excluded.", DescribeRole.Theorem),
            Node("rotationavoidanceconsecutive-positive-middle-endpoint-count", "Separated endpoints and a product count", "positive_middle_endpoint_count", "Let first be at least two, first plus one be less than last, and last be less than size. Permutations of one through size beginning with first and ending with last, and containing 2143 in exactly the uncut rotation, number (first - 1) times (size - last). The normal form is determined by an independent split in each of the lower and upper intervals.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
