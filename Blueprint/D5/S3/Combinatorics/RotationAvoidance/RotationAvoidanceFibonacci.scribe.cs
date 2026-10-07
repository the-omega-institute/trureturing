using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceFibonacciDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacci.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two classical pattern avoidance classes have cardinalities given by odd-indexed Fibonacci numbers and powers of two.",
        H("RotationAvoidanceFibonacci"),
        Blocks(
            Node("rotationavoidancefibonacci-fibonacci-count-theorem", "Enumeration of permutations avoiding 213 and 4132", "fibonacci_count", "For every positive integer n, the number of permutations of one through n avoiding 213 and 4132 is F_(2n minus one), where F_0 is zero, F_1 is one and each subsequent Fibonacci number is the sum of the preceding two. Decomposition at the minimum uses the classical avoidance family, invariance of containment under increasing relabelling, and the fact that separated low and high blocks have interval supports.", DescribeRole.Theorem),
            Node("rotationavoidancefibonacci-skew-block-binary-count-theorem", "Enumeration of permutations avoiding 132 and 213", "skew_block_binary_count", "For every positive integer n, the number of permutations of one through n avoiding both 132 and 213 is 2^(n - 1). Permutations avoiding 132 and 213 are concatenations of increasing interval blocks ordered from high values to low values. The increasing-block characterization and its converse identify such permutations with compositions of n.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
