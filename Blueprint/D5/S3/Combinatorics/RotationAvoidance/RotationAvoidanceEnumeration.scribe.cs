using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceEnumerationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceEnumeration.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The permutations avoiding 123 and 3412 are enumerated by separating decreasing prefixes from prefixes containing an ascent.",
        H("RotationAvoidanceEnumeration"),
        Blocks(
            Node("rotationavoidanceenumeration-ascending-positive-suffix-count-theorem", "Enumeration with a fixed position of the minimum", "ascending_positive_suffix_count", "For a nonnegative integer w and a positive integer s, consider permutations of one through w plus s plus one that avoid 123 and 3412, have exactly w entries before one and have a prefix before one that is not strictly decreasing. Their number is 2^w - w - 1.", DescribeRole.Theorem),
            Node("rotationavoidanceenumeration-ascending-decreasing-prefix-count-theorem", "Enumeration with a decreasing prefix before the minimum", "ascending_decreasing_prefix_count", "For every nonnegative integer s, the number of permutations of one through s plus one avoiding 123 and 3412 whose prefix before one is strictly decreasing is 2^s. An empty prefix is permitted.", DescribeRole.Theorem),
            Node("rotationavoidanceenumeration-ascending-count-theorem", "Enumeration of permutations avoiding 123 and 3412", "ascending_count", "For every nonnegative integer n, the number of permutations of one through n avoiding 123 and 3412 is 2^(n + 1) - 2n - 1 - C(n + 1, 3), where C(n + 1, 3) is the binomial coefficient with upper argument n plus one and lower argument three. All subtractions are natural-number subtractions.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
