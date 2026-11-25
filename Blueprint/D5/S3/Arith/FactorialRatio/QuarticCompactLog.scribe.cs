using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class QuarticCompactLogDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/QuarticCompactLog.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quadratic logarithmic gap",
        H("Quartic compact factorial gcd"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quartic-compact-log-gap"),
                DeclarationHandle.Create(Prefix + "quartic_compact_log_gap"),
                H("Quadratic logarithmic gap"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Write the logarithmic gap as the logarithm of the integral quotient of the "
                    + "compact gcd by the tail LCM. Expand it as a sum of exponent differences "
                    + "weighted by log p. The small primes contribute at most 3(log 4+4)r^2 "
                    + "by the Chebyshev psi bound. Finite summation by parts bounds the sum of "
                    + "log p divided by sqrt(p) up to s by 2(log 4+4)sqrt(s). Since s<r^2, "
                    + "the large primes contribute at most 8(log 4+4)r^2."))),
                DescribeRole.Theorem))));
}
