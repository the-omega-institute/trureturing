using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Finite;

internal sealed class RobinRow01Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/Finite/RobinRow01.";
    private static readonly LibraryNoteRef Robin1984Source =
        LibraryNoteRef.Create("D5/L/Analytic/kimihiro2026robin1984");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unique optimizer at the original Robin1984 Row 01 price, a strict log margin reserve on log-height [22,36], and the finite Robin inequality through 321253732800.",
        H("Robin1984 Row 01 at its original price"),
        Blocks(
            Paragraph(Text("Write sigma(n) for the sum of divisors of n and gamma for the Euler–Mascheroni constant. All logarithms are natural. For positive n the original objective at price q is G(q,n) = log(sigma(n)/n) - q log(n), and the Robin log margin is M(n) = gamma + log(log(log(n))) - log(sigma(n)/n).")),
            Paragraph(Text("The price and layer cutoffs [28, 6, 3, 2, 2, 2] come from Jonas Whidden's Robin1984 certificate robinFiniteRow01. Its original log-height window is [22117363/1000000, 35788699/1000000]. The pinned source is https://github.com/kimihiro64/Robin1984/blob/5ce18bf3487c68d9353276ef5811057f60d17808/Robin1984/Finite/Certificates/Row01.lean")),
            Describe.Lean(
                DescribeId.Create("row01-price"), DeclarationHandle.Create(Prefix + "row01Price"),
                H("Exact Row 01 price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Robin1984Source),
                Blocks(Paragraph(Text("The original price q is the positive real rational 2565510579241/250000000000000."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("row01-integer"), DeclarationHandle.Create(Prefix + "row01Integer"),
                H("Row 01 integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural integer N is 321253732800, the product 2^6 * 3^3 * 5^2 * 7 * 11 * 13 * 17 * 19 * 23."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("row01-optimal-iff"), DeclarationHandle.Create(Prefix + "row01_optimal_iff"),
                H("Unique optimizer at the original price"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural m >= 1, G(q,j) <= G(q,m) for all natural j >= 1 if and only if m = N. Exact rational logarithm bounds separate the marginal from q on both sides of each cutoff. Monotonicity in the base and layer gives strict signs on all prime layers, forcing the prime exponents of every optimizer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("row01-log-margin-reserve"), DeclarationHandle.Create(Prefix + "robin_log_margin_fixed_price_row01"),
                H("Strict log margin reserve"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n with 22 <= log(n) <= 36, the strict bound is 1/80 + G(q,N) - G(q,n) < M(n). This keeps the exact objective deficit at the original price. Rational bounds give a strict reserve at heights 22 and 36. Concavity of H ↦ gamma + log(log(H)) propagates the bound over the whole closed interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("original-robin-through-row01"), DeclarationHandle.Create(Prefix + "original_robin_through_row01"),
                H("Robin's inequality through 321253732800"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural n with 5040 < n <= 321253732800, sigma(n) < exp(gamma) * n * log(log(n)) unconditionally. Whidden's nativeRobinInequality_finite_log gives the wider external range with log(n) < 74500. This derivation uses the original-price optimizer intervals. At each price at least q the optimizer endpoints divide N. Among endpoints above 5040, those with at most eight distinct prime factors satisfy the existing few-prime bound. Every remaining endpoint above 5040 is a multiple of 5354228880, which places its log-height in [22,36]. The strict reserve certifies those endpoints, and the original optimizer interval transfer then gives the inequality for every integer in the stated range."))),
                DescribeRole.Theorem))));
}
