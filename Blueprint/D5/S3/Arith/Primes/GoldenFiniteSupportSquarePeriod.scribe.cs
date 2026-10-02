using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class GoldenFiniteSupportSquarePeriodDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sink primes determine the exact square-period ratio on finite prime support.",
        H("Finite-support square periods"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-finite-support-square-period"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/GoldenFiniteSupportSquarePeriod.golden_finite_support_square_period"),
                H("Square-period ratio and sinks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let S be a nonempty finite set of primes greater than five and let M "
                    + "be their product. Write pi(m) for the order of the Fibonacci matrix "
                    + "modulo m, pi_s(m) for the order of its s-th power, and h_p for "
                    + "the p-adic valuation of F_(rho(p)), where rho(p) is the first "
                    + "positive Fibonacci index divisible by p. Draw p to q when p "
                    + "divides pi(q), and call p a sink if no such q belongs to S. "
                    + "Every edge increases its prime label, so the directed graph has "
                    + "no nonempty cycle and its largest prime is a sink. For every "
                    + "positive s coprime to M, pi_s(M^2) divided by pi_s(M) is the "
                    + "product of exactly those sink primes whose depth h_p equals one. "
                    + "The two stride periods are equal exactly when every sink has "
                    + "depth at least two; equality therefore forces depth at least "
                    + "two for the largest prime of S. The equality criterion imposes "
                    + "no depth condition on nonsinks."))),
                DescribeRole.Theorem))));
}
