using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciHalfBinomialValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized binomial coefficient one half choose j has an exact 2-adic valuation.",
        H("Dyadic Valuation of Half-Binomial Coefficients"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-half-binomial-valuation"),
                DeclarationHandle.Create("D5/S3/Arith/Primes/FibonacciHalfBinomialValuation.half_binomial_two_adic_valuation"),
                H("Exact half-binomial valuation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural j, the 2-adic valuation of the rational generalized binomial coefficient one half choose j "
                    + "equals minus j minus the 2-adic valuation of j factorial. Multiplying that coefficient by 2 to the j "
                    + "times j factorial gives a product of odd integers, so the coefficient is nonzero and all of its dyadic "
                    + "denominator is accounted for by those two factors."))),
                DescribeRole.Theorem))));
}
