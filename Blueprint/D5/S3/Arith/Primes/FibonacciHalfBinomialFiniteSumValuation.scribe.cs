using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Primes;

internal sealed class FibonacciHalfBinomialFiniteSumValuationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite half-binomial sum has the last term's dyadic valuation when its last integer coefficient is odd.",
        H("Dyadic Dominance in a Half-Binomial Sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fibonacci-half-binomial-finite-sum-valuation"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Primes/FibonacciHalfBinomialFiniteSumValuation.half_binomial_finite_sum_valuation"),
                H("Exact valuation of the finite sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let n be a positive natural number and c any integer sequence whose coefficient at n is odd. "
                    + "Sum, for m from zero through n, the rational generalized binomial coefficient one half choose m "
                    + "times c at m. The 2-adic valuation of this sum equals minus n minus the 2-adic valuation "
                    + "of n factorial. The last term has this valuation; each earlier nonzero term has strictly "
                    + "greater valuation, and zero terms do not change the sum."))),
                DescribeRole.Theorem))));
}
