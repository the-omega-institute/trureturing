using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Permutation;

internal sealed class LeSaulnierVijayLowerDensityRefutationOrderDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/Permutation/LeSaulnierVijayLowerDensityRefutationOrder.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversing a fixed number of binary digits gives a finite order in which no "
            + "nonconstant three-term arithmetic progression occurs as a subsequence.",
        H("Finite binary reversal avoids arithmetic progressions"),
        Blocks(
            Node("binary-rank", "Binary reversal", "rank",
                "For zero bits the rank is zero. For one more bit, the lowest bit contributes "
                    + "two to the power of the previous bit count, and the remaining contribution "
                    + "is the rank of the quotient by two with the previous bit count.",
                DescribeRole.Definition),
            Node("rank-bound", "The rank fits within the bit bound", "rank_lt",
                "For every bit count and natural input, the rank is strictly below two "
                    + "raised to the bit count.", DescribeRole.Theorem),
            Node("rank-injection", "Injectivity on bounded inputs", "rank_injective",
                "If both inputs are strictly below two raised to the bit count and their "
                    + "ranks agree, the inputs agree. The highest reversed digit determines "
                    + "parity, and induction determines the quotients by two.", DescribeRole.Theorem),
            Node("rank-no-ap", "No monotone arithmetic progression", "rank_no_ap",
                "For any three inputs strictly below the same power of two whose endpoints "
                    + "sum to twice the middle input, the three ranks cannot be strictly "
                    + "increasing. The endpoints have the same parity. If the middle parity "
                    + "differs, its rank is an extreme; otherwise division by two preserves "
                    + "the progression and induction applies.", DescribeRole.Theorem)),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
