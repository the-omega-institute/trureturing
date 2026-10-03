using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceCounts.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cutting a circular permutation at its minimum reduces several classes to classical pattern avoidance and decompositions around the minimum.",
        H("RotationAvoidanceCounts"),
        Blocks(
            Node("rotationavoidancecounts-minimum-rooted-reductions-theorem", "Three reductions at the minimum", "minimum_rooted_reductions", "Let n be nonnegative and suppose that placing one before a list t gives a permutation of one through n plus one. This permutation is a circular avoider of 1234 exactly when t avoids 123 and 3412; it is a circular avoider of 1342 exactly when t avoids 231, 2134 and 4213; and it is a circular avoider of 1324 exactly when t avoids 213 and 4132.", DescribeRole.Theorem),
            Node("rotationavoidancecounts-binary-extreme-count-theorem", "Enumeration of permutations avoiding 213 and 231", "binary_extreme_count", "For every positive integer n, the number of permutations of one through n avoiding both 213 and 231 is 2^(n - 1).", DescribeRole.Theorem),
            Node("rotationavoidancecounts-minimum-split-fibonacci-theorem", "Decomposition of avoidance of 213 and 4132", "minimum_split_fibonacci", "Let p be the concatenation of a list L, the entry one and a list R, with no repeated entries and with every entry in L and R greater than one. Then p avoids 213 and 4132 if and only if L avoids both patterns, every entry of R is less than every entry of L, and either L is empty and R avoids both patterns, or L is nonempty and R is strictly increasing.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
