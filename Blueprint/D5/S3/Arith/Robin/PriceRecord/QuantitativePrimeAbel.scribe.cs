using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class QuantitativePrimeAbelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real-endpoint four-term prime-counting expansion.",
        H("Quantitative counting and finite Euler deficits"),
        Blocks(
            Paragraph(Text("A quantitative theta remainder and finite Abel summation give the real-endpoint prime-counting expansion through its residual coefficient 24. The same literal finite prime intervals carry the nonlinear Euler deficit estimates used by the real-image infimum limit.")),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-theta-error-log-power"),
                DeclarationHandle.Create(Prefix + "theta_error_log_power"), H("Theta remainder at every fixed log power"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural N, theta(x)-x is little-o of x/log(x)^N at real atTop, using the actual MediumPNT exponent 1/10 and the frozen psi-minus-theta transfer."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-counting-polynomial"),
                DeclarationHandle.Create(Prefix + "countingPolynomial"), H("Four-term counting polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("countingPolynomial x is x*(1/log x + 1/log(x)^2 + 2/log(x)^3 + 6/log(x)^4)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-prime-counting-four-terms"),
                DeclarationHandle.Create(Prefix + "prime_counting_four_terms"), H("Four terms with residual coefficient 24"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real-endpoint residual (primeCount x-countingPolynomial x)/(x/log(x)^5) tends to 24 atTop. The primeCount definition includes the floor endpoint and no separate pi hypothesis is introduced."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-primecount"),
                DeclarationHandle.Create(Prefix + "primeCount"), H("primeCount"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real endpoint counting function is Nat.primeCounting at the natural floor of t, cast to the reals. The floor convention fixes all endpoint ties."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-primeinterval"),
                DeclarationHandle.Create(Prefix + "primeInterval"), H("primeInterval"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite interval consists of primes in the natural Ioc from floor(y) to floor(z), so it represents the strict lower and included upper real endpoints y<p<=z."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-squaresum"),
                DeclarationHandle.Create(Prefix + "squareSum"), H("squareSum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite square sum is the sum of p^-2 over that literal prime interval, with no infinite-tail replacement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-logarithmictail"),
                DeclarationHandle.Create(Prefix + "logarithmicTail"), H("logarithmicTail"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The logarithmic Euler tail is the finite sum of -log(1-p^-2) on the same interval as the square sum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-log-deficit-bounds"),
                DeclarationHandle.Create(Prefix + "log_deficit_bounds"), H("log deficit bounds"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For 0<=q<1, the pinned elementary logarithm inequalities give q<=-log(1-q)<=q/(1-q), including q=0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-finite-logarithmic-tail-squeeze"),
                DeclarationHandle.Create(Prefix + "finite_logarithmic_tail_squeeze"), H("finite logarithmic tail squeeze"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For y>1 and every real z, the logarithmic Euler tail lies between the square sum and squareSum/(1-y^-2). The strict lower endpoint supplies a uniform positive denominator; empty intervals remain covered."))), DescribeRole.Theorem)
        )));
}
