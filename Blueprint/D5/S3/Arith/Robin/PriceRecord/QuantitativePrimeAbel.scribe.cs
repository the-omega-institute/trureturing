using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class QuantitativePrimeAbelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/PriceRecord/QuantitativePrimeAbel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real-endpoint four-term prime-counting expansion.",
        H("Native scoped implementation"),
        Blocks(
            Paragraph(Text("Native compiled scope only. The consumed theta remainder transfer and private finite FTC ratio helper support the original quantitative statements. This delivery does not claim final16, RH, or exact-infimum admission.")),
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
            Describe.Lean(DescribeId.Create("quantitativeprimeabel-prime-counting-four-terms-uniform"),
                DeclarationHandle.Create(Prefix + "prime_counting_four_terms_uniform"), H("Uniform coefficient-25 consequence"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("One threshold X>1 gives the uniform absolute error bound 25*x/log(x)^5 for every real x>=X. The finite-tail consumer uses this moving-endpoint envelope."))), DescribeRole.Theorem)
        )));
}
