using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class DigitCapLowerExponentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Digit/DigitCapLowerExponent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Below twice the radix, every input ell^s-1 has a single bounded-digit "
            + "representation, and the lower logarithmic growth exponent is zero.",
        H("Singleton representations and the zero lower growth exponent"),
        Blocks(
            Node("lower", "Extended-real every-tail lower limit", "lowerExponent",
                "lowerExponent k ell is the supremum, over natural N with 2≤N, of the "
                + "infimum, over every natural n with N≤n, of the real readout "
                + "log(count k ell n)/log n embedded in EReal. It is the lower-limit "
                + "counterpart of the upper exponent, taken over entire natural tails "
                + "with no finiteness premise.", DescribeRole.Definition),
            Node("singleton", "One representation of ell^s-1", "count_pow_sub_one",
                "For natural ell, k and s with 2≤ell and ell−1≤k≤2·ell−2, "
                + "count k ell (ell^s−1)=1; the case s=0 is the empty representation "
                + "of zero. Since ell^s−1<ell^s, every coefficient at a position at least s "
                + "vanishes. The digits ell−1 at positions 0,...,s−1 have weighted value "
                + "ell^s−1. Conversely, reducing the weighted sum modulo ell gives "
                + "a(0)≡ell−1, and a(0)≤2·ell−2<2·ell−1 forces a(0)=ell−1. Cancelling "
                + "this digit and dividing by ell leaves the same problem with s−1 "
                + "positions, so induction forces every digit. Existence of some "
                + "representation for k≥ell−1 then gives cardinality exactly one.",
                DescribeRole.Theorem),
            Node("zero", "The lower exponent vanishes", "lowerExponent_eq_zero",
                "For natural ell and k with 2≤ell and ell−1≤k≤2·ell−2, "
                + "lowerExponent k ell=0. For every n≥2 the count is at least one and "
                + "log n>0, so every readout from two on is nonnegative and every tail "
                + "infimum is at least zero. Given N≥2, the input ell^(N+1)−1 is at "
                + "least N and has readout log 1/log(ell^(N+1)−1)=0, so every tail infimum is at "
                + "most zero. Hence every tail infimum, and their supremum, equal zero. "
                + "Consequently, whenever ell−1≤k≤2·ell−3 both lowerExponent k ell and "
                + "lowerExponent (k+1) ell are zero; at radix four this covers k=5 and "
                + "k=6.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("digit-cap-lower-exponent-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
