using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class NiuQ15AnalyticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/NiuQ15Analytic.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform bounds and normalized limits for the rectangular first-descent distribution.",
        H("Limits of the Rectangle Tail and Point Laws"),
        Blocks(
            Node("niuq15analytic-finitetail", "Finite survival function", "finiteTail",
                "For r at most n, the finite tail is the binomial coefficient choose(r + K - 1, K - 1) times the product of (n - j)/(K n - j) over j from zero through r minus one. For r above n the tail is zero.",
                DescribeRole.Definition),
            Node("niuq15analytic-limittail", "Limiting survival function", "limitTail",
                "The limiting tail at r is choose(r + K - 1, K - 1) divided by K to the power r.",
                DescribeRole.Definition),
            Node("niuq15analytic-limitmass", "Limiting point mass", "limitMass",
                "The limiting mass at r is r times choose(r + K - 1, K - 2) divided by K to the power r + 1.",
                DescribeRole.Definition),
            Node("niuq15analytic-finitetail-le-bound", "Summable bound independent of width", "finiteTail_le_bound",
                "For K at least two, the absolute value of the finite tail has a width-independent bound of one at r = 0 and (3/4) to the power r - 1 for r at least one. The finite tails are nonnegative and no greater than the limiting tails.",
                DescribeRole.Theorem),
            Node("niuq15analytic-tendsto-finitetail", "Limit of each tail", "tendsto_finiteTail",
                "For K at least two and each natural threshold r, the finite tail tends to the limiting tail as n tends to infinity.",
                DescribeRole.Theorem),
            Node("niuq15analytic-hassum-limitmass", "Normalization of the point law", "hasSum_limitMass",
                "When K is at least two, the sum over all natural r of the limiting masses is one. The adjacent-tail differences telescope and the limiting tail tends to zero.",
                DescribeRole.Theorem),
            Node("niuq15analytic-hassum-even-limitmass", "Sum of the even masses", "hasSum_even_limitMass",
                "For K at least two, the sum of the limiting masses at even indices is (K/(K + 1)) to the power K. Pairing adjacent tails yields the negative binomial series at -1/K.",
                DescribeRole.Theorem),
            Node("niuq15analytic-tendsto-alternating-finitetail", "Limit of the alternating tail sum", "tendsto_alternating_finiteTail",
                "For K at least two, the alternating sum of the finite tails tends to (K/(K + 1)) to the power K. The same summable bound applies at every width.",
                DescribeRole.Theorem)
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, string prose,
        DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
