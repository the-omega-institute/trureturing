using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciHalfBinomialCatalanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of the formal square root of one plus X have a signed Catalan form with only powers of two in the denominator.",
        H("Catalan Formula for Half-Binomial Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-half-binomial-catalan"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciHalfBinomialCatalan.half_binomial_catalan"),
                H("Signed dyadic Catalan coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every nonnegative n, the generalized binomial coefficient one half choose n plus one equals "
                    + "negative one to the n times the n-th Catalan number divided by two to the power two n plus one. "
                    + "Consequently, multiplying the coefficient by that power of two gives an integer. The proof "
                    + "transports the Catalan generating series to rational coefficients and rescales its variable "
                    + "by negative one quarter. The resulting series gives a square root of one plus X with "
                    + "constant coefficient one, so it agrees with the formal binomial series."))),
                DescribeRole.Theorem))));
}
