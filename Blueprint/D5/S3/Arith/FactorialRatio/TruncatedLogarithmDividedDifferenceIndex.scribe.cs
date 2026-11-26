using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class TruncatedLogarithmDividedDifferenceIndexDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Arith/FactorialRatio/TruncatedLogarithmDividedDifferenceIndex";

    private static DocumentBlock Entry(string id, string name, string title, string statement, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), role);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Counting the prefix least common multiple factors gives an exact positive integer for the factor-four prime tent.",
        H("Divided-difference LCM indices"),
        Blocks(
            Entry("difference-index", "differenceIndex", "Product of prefix least common multiples",
                "For natural n and r, I(n,r) is the product of lcmUpto(floor(d/r)) over 0 <= d < n. "
                + "Division uses Lean's natural division, which is zero when r=0. "
                + "The product is one when n=0.", DescribeRole.Definition),
            Entry("difference-log", "log_differenceIndex", "Exact logarithm of the index",
                "For natural n and positive natural r, log(I(n,r)) is the sum over 0 <= q < n "
                + "of max(n-rq,0) times the von Mangoldt value at q. "
                + "The logarithm of each prefix LCM is a Chebyshev psi sum. "
                + "Exchanging the two finite sums counts the d with rq <= d < n.", DescribeRole.Theorem),
            Entry("difference-valuation", "factorization_differenceIndex", "Exact prime valuation of the index",
                "For natural n, positive natural r and prime p, the p-valuation of I(n,r) is "
                + "the sum over 0 <= a < n of max(n-r*p^(a+1),0). "
                + "The valuation of a prefix LCM counts the powers p^(a+1) up to its cutoff. "
                + "For each such power the number of eligible d is the length of the interval from "
                + "r*p^(a+1) up to, but excluding, n.", DescribeRole.Theorem),
            Entry("tent-weight", "tentWeight", "Factor-four tent weight",
                "For natural x and q, the weight is zero for q <= x, is 2*(q-x) for x < q <= 2*x, "
                + "and is max(4*x-q,0) for q > 2*x.", DescribeRole.Definition),
            Entry("relative-index", "relativeIndex", "Relative divided-difference index",
                "At each natural x, the relative index is the natural quotient of "
                + "I(4*x,1)^2 * I(4*x,4) by I(4*x,2)^3.", DescribeRole.Definition),
            Entry("exact-quotient", "relativeIndex_spec", "Positive exact quotient",
                "For every natural x the denominator I(4*x,2)^3 divides the numerator "
                + "I(4*x,1)^2 * I(4*x,4). Multiplying the relative index by the denominator gives the numerator, "
                + "and the relative index is strictly positive. At every prime power, the numerator's exponent "
                + "contribution exceeds or equals the denominator's contribution by twice the tent weight.",
                DescribeRole.Theorem),
            Entry("relative-valuation", "factorization_relativeIndex", "Prime-power tent valuation",
                "For every natural x and every prime p, the p-valuation of the relative index is the sum over "
                + "0 <= a < 4*x of twice the tent weight at p^(a+1). Each term of the numerator valuation "
                + "is the corresponding denominator term plus twice this weight, so the denominator cancels.",
                DescribeRole.Theorem),
            Entry("relative-log", "log_relativeIndex", "Exact tent logarithm",
                "For every natural x, the logarithm of the relative index is twice the sum over "
                + "0 <= q < 4*x of the tent weight at q times the von Mangoldt value at q. "
                + "The three index logarithms have the same finite cutoff. Applying the tent identity to each "
                + "summand and cancelling the denominator logarithm gives the formula. The formulas include "
                + "all primes and their powers, with empty sums and relative index one at x=0.",
                DescribeRole.Theorem))));
}
