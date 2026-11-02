using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil;

internal sealed class PrimeValuationGapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/PrimeValuationGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded valuations at a fixed prime leave a positive asymptotic Robin margin.",
        H("Fixed Prime Valuation Gap"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("retention-positive"),
                DeclarationHandle.Create(Prefix + "retention_pos"),
                H("Positive retained local factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every natural prime p and every natural exponent a give a strictly positive factor 1-p^(-(a+1)), including a=0."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("normalized-prime-part"),
                DeclarationHandle.Create(Prefix + "normalized_sigma_pow_mul"),
                H("Normalized divisor sum after adjoining a prime power"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime p, every natural m coprime to p, and every natural exponent a, sigma one of p^a m divided by p^a m equals the exact geometric local factor times sigma one m divided by m. The case a=0 is retained."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-loglog-scale"),
                DeclarationHandle.Create(Prefix + "tendsto_loglog_scale"),
                H("A fixed positive scale preserves log-log asymptotics"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every positive real c, log(log(c n)) divided by log(log n) tends to one along natural n. The scale is fixed before the limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-layer-ratio"),
                DeclarationHandle.Create(Prefix + "prime_power_abundancy_ratio"),
                H("Exact prime layer gain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a prime p, a nonzero natural n, and a natural b, let a be "
                    + "the p-adic valuation of n. The ratio of the abundancy of p^b n "
                    + "to that of n is (1-p^(-(a+b+1)))/(1-p^(-(a+1))). "
                    + "Multiplicativity cancels the common factor coprime to p."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-layer-window"),
                DeclarationHandle.Create(Prefix + "prime_power_abundancy_gain"),
                H("Uniform gain on an exponent window"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When a is at most A, the gain is bounded below by "
                    + "(1-p^(-(A+b+1)))/(1-p^(-(A+1))). The comparison follows "
                    + "from the nonnegativity of (p^(-(a+1))-p^(-(A+1)))(1-p^(-b))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-local-gap"),
                DeclarationHandle.Create(Prefix + "prime_valuation_gap_pos"),
                H("Positive logarithmic defect"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every fixed prime p and natural A, the number "
                    + "-log(1-p^(-(A+1))) is strictly positive. The number depends "
                    + "on p and A."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-valuation-envelope"),
                DeclarationHandle.Create(Prefix + "bounded_prime_valuation_robin_ratio"),
                H("Sharp asymptotic ratio bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive epsilon there is a threshold N at least 5041 "
                    + "such that every n at least N with valuation at most A has Robin "
                    + "ratio at most 1-p^(-(A+1))+epsilon. A fixed layer count b is "
                    + "selected using geometric decay; the threshold is then obtained "
                    + "for that b from the Gronwall upper envelope and the logarithmic "
                    + "scale limit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bounded-valuation-margin"),
                DeclarationHandle.Create(Prefix + "bounded_prime_valuation_robin_margin_gap"),
                H("Asymptotic Robin margin"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive epsilon, all sufficiently large integers with "
                    + "p-adic valuation at most A have logarithmic Robin margin at least "
                    + "-log(1-p^(-(A+1)))-epsilon. The threshold includes the Robin "
                    + "domain n at least 5041. The conclusion is unconditional and "
                    + "does not specify a numerical threshold."))),
                DescribeRole.Theorem))));
}
