using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenPrimePeriodBoundsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden Frobenius gives prime residue-period bounds for the Fibonacci matrix.",
        H("Golden Prime Period Bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-fibonacci-matrix-period-bounds"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenPrimePeriodBounds.golden_prime_period_bounds"),
                H("Split and inert period bounds"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each prime greater than five, the Fibonacci matrix period "
                    + "divides p-1 when five is a quadratic residue modulo p, and "
                    + "divides 2(p+1) when it is a nonresidue. In either case the "
                    + "period is not divisible by p. The proof transports the "
                    + "Fibonacci entry-point congruence through the faithful "
                    + "golden multiplication representation."))),
                DescribeRole.Theorem))));
}
