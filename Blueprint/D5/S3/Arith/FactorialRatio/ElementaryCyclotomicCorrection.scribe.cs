using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio;

internal sealed class ElementaryCyclotomicCorrectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/ElementaryCyclotomicCorrection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact factorial and residue correction to the cyclotomic carry product.",
        H("Cyclotomic factorial correction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("residue-indicator"),
                DeclarationHandle.Create(Prefix + "levelIndicator"),
                H("Residue indicator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The indicator is one at conductors r congruent to 1 modulo 4 for which the remainder "
                        + "of N modulo r reaches floor((r+2)/4). It is zero at every other level."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("level-deficit"),
                DeclarationHandle.Create(Prefix + "levelDeficit"),
                H("Prime-power deficit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The deficit is the exceptional index count plus N at level two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("closed-level-deficit"),
                DeclarationHandle.Create(Prefix + "levelDeficit_prime_pow"),
                H("Closed prime-power deficit count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a prime p and a positive exponent t, the count is the sum of the contribution N at "
                        + "p^t = 2, the floor N/p^t at odd p, and the residue indicator.")),
                    Paragraph(Text(
                        "At r congruent to 1 modulo 4, exceptional indices are multiples of r. The last "
                        + "multiple is counted precisely when the remainder of N reaches the cutoff. At r "
                        + "congruent to 3 modulo 4, the first exceptional index is r minus the cutoff. The cutoff "
                        + "then brings each such index to a positive multiple of r. The two progression "
                        + "bijections hold for empty ranges as well."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-factor"),
                DeclarationHandle.Create(Prefix + "RStar"),
                H("Residual integer factor"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Multiply p once for each selected prime power p^t up to 4N+1. Several selected powers "
                        + "of the same prime contribute separate copies of that prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("factorial-identity"),
                DeclarationHandle.Create(Prefix + "EStar_eq_two_pow_digit_sum_mul_factorial_mul_RStar"),
                H("Exact factorial correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The exceptional factor equals 2 raised to the binary digit sum of N, times N "
                        + "factorial, times the residual factor.")),
                    Paragraph(Text(
                        "Compare prime valuations. Legendre's factorial formula sums the odd level floors. At "
                        + "two, the exceptional valuation is N and the factorial valuation is N minus the binary "
                        + "digit sum."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("correction-multinomial"),
                DeclarationHandle.Create(Prefix + "correctionMultinomial"),
                H("Correction multinomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the four parts N, N, N and N+1, divide the factorial of 4N+1 by "
                        + "the product of three copies of N factorial and one copy of (N+1) factorial."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-divisibility"),
                DeclarationHandle.Create(Prefix + "RStar_dvd_correctionMultinomial"),
                H("Residual factor divides the multinomial"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The residual integer factor divides the correction multinomial for every N.")),
                    Paragraph(Text(
                        "At each prime power, the multinomial valuation counts floors from its factorial "
                        + "quotient. After cancelling the quotient of N by the conductor, the floor difference "
                        + "depends only on the remainder. Each selected conductor contributes at least one to "
                        + "this difference."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("residual-log-bound"),
                DeclarationHandle.Create(Prefix + "log_RStar_bounds"),
                H("Linear logarithmic bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The logarithm of the residual factor lies between zero and (4N+1) log 4.")),
                    Paragraph(Text(
                        "Divisibility bounds the residual factor by the positive multinomial. The multinomial "
                        + "is one term in the expansion of four raised to 4N+1, obtained by raising "
                        + "the sum of four ones to that exponent."))),
                DescribeRole.Theorem))));
}
