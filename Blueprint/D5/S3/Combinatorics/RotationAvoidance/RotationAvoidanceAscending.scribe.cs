using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceAscendingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceAscending.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Permutations avoiding 123 and 3412 admit descriptions by a decreasing interval after the minimum and shuffles of the entries below and above that interval.",
        H("RotationAvoidanceAscending"),
        Blocks(
            Node("rotationavoidanceascending-minimum-split-ascending-theorem", "Decomposition of avoidance of 123 and 3412", "minimum_split_ascending", "Let p be the concatenation of a list L, the entry one and a list R, with no repeated entries and with every entry of L and R greater than one. Then p avoids 123 and 3412 if and only if L avoids both patterns, R is strictly decreasing, and every increasing pair of entries in L, taken in their order of appearance, has every entry of R strictly between its two values.", DescribeRole.Theorem),
            Node("rotationavoidanceascending-ascending-middle-interval-theorem", "The suffix interval and two decreasing subsequences", "ascending_middle_interval", "Suppose that the concatenation of L, the entry one and R is a permutation of one through n avoiding 123 and 3412, and L is not strictly decreasing. Every integer strictly between two values belonging to R also belongs to R. For every value m in R, the subsequence of L consisting of entries less than m and the subsequence consisting of entries greater than m are both strictly decreasing.", DescribeRole.Theorem),
            Node("rotationavoidanceascending-shuffle-count-theorem", "Enumeration of shuffles of two separated lists", "shuffle_count", "Let a Boolean predicate be true on every entry of a list L and false on every entry of a list H. The number of lists that are permutations of the concatenation of L and H and whose subsequences selected by the predicate and its negation are respectively L and H is the binomial coefficient with upper argument the sum of the lengths of L and H and lower argument the length of L. Repeated entries within either list are allowed.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
