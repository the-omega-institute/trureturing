using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceLinearDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceLinear.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The classes avoiding 231, 2134 and 4213 decompose at their maximum into two ordered blocks.",
        H("RotationAvoidanceLinear"),
        Blocks(
            Node("rotationavoidancelinear-maximum-split-binary-theorem", "Decomposition at the maximum", "maximum_split_binary", "Let p be the concatenation of a list L, an entry m and a list R, with no repeated entries and with every entry of L and R less than m. Then p avoids 231, 2134 and 4213 if and only if every entry of L is less than every entry of R, both L and R avoid 213 and 231, and either L is strictly increasing or R is strictly decreasing.", DescribeRole.Theorem),
            Node("rotationavoidancelinear-binary-separator-count-theorem", "Enumeration of permutations avoiding 231, 2134 and 4213", "binary_separator_count", "For every nonnegative integer n, the number of permutations of one through n avoiding 231, 2134 and 4213 is 2^n - n. Increasing relabelling preserves containment, and the separated blocks occupy consecutive low and high intervals. The resulting classical avoidance decomposition combines the counts for avoiding 213 and 231.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
