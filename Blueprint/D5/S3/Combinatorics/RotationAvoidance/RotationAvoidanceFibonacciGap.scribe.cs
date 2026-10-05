using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.RotationAvoidance;

internal sealed class RotationAvoidanceFibonacciGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/RotationAvoidance/RotationAvoidanceFibonacciGap.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/egecioglu2026rotations");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The 1324 and 1423 classes with one containing cut have different cardinalities.",
        H("RotationAvoidanceFibonacciGap"),
        Blocks(
            Node("rotationavoidancefibonaccigap-fibonacci-lt-layered", "Strict inequality from the Fibonacci class to the layered class", "fibonacci_lt_layered", "For every size at least seven, the number of circular permutations rooted at one with exactly one rotation containing 1324 is strictly less than the corresponding number for 1423. Endpoint decompositions express both totals through odd-indexed Fibonacci factors and binomial counts; comparison of these sums gives the strict inequality.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
