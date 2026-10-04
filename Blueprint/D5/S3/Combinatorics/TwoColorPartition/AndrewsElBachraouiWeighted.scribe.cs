using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TwoColorPartition;

internal sealed class AndrewsElBachraouiWeightedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TwoColorPartition/AndrewsElBachraouiWeighted.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Combinatorics/andrews2025positive");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weighted and parity-restricted alternating odd divisor sums satisfy explicit bounds.",
        H("Weighted and Parity-Restricted Divisor Sums"),
        Blocks(
            Node("andrews-el-bachraoui-weighted-weighted-alternating-odd-divisor-sum-bound", "Sign and square bound for the weighted sum", "weighted_alternating_odd_divisor_sum_bound", "For every natural number n, let W be the sum over i from zero through n of (-1) raised to n minus i, multiplied by n minus i plus one and by the number of positive divisors of 2i plus one. Then W multiplied by (-1) raised to n is nonnegative and is at most the square of the integer quotient of the natural square root of 2n plus three, increased by one, divided by two. A weighted character convolution and a hyperbola decomposition give both inequalities.", DescribeRole.Theorem),
            Node("andrews-el-bachraoui-weighted-parity-alternating-odd-divisor-sum-bound", "Square-root bound for the parity-restricted sum", "parity_alternating_odd_divisor_sum_bound", "For every natural number n, sum over the integers i from zero through n having the same parity as n the number of positive divisors of 2i plus one, multiplied by (-1) raised to the integer quotient of n minus i divided by two. The absolute value of this sum is at most the natural square root of 2n plus one, increased by two. Characters modulo eight express the parity restriction as signed divisor convolutions.", DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
