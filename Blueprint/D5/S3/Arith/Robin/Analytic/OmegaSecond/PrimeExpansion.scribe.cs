using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class PrimeExpansionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-counting coefficients and the residual budget at the second distinct-prime threshold.",
        H("Prime expansion and second-threshold budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-term-polynomial"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.countingThreeTerms"),
                H("Three-term counting polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The polynomial is P/log(P)+P/log(P)^2+2P/log(P)^3. The prime count uses the natural floor of the real endpoint P."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-term-expansion"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_three_terms"),
                H("Three-term prime-counting expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After subtracting the three-term polynomial, division by P/log(P)^4 gives limit six as P tends to positive infinity. This follows from the existing four-term expansion with its next residual coefficient twenty-four."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counting-error-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.prime_counting_error_bound"),
                H("Uniform eventual counting error"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all sufficiently large real P, the absolute difference between the prime count and P/log(P) is at most 3P/log(P)^2. The same bound applies at every endpoint beyond a single fixed threshold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("budget"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget"),
                H("Second-threshold budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The budget is P-theta(P)+(primeCount(P)-P/log(P)-P/log(P)^2)*log(P). It retains the exact prime-counting and Chebyshev terms before normalization."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("budget-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/PrimeExpansion.budget_limit"),
                H("Exact cancellation and residual coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The budget divided by P/log(P)^2 tends to two. The first two prime-counting terms cancel the threshold exactly; the third coefficient supplies two, while the Chebyshev error vanishes on this scale.")),
                    Paragraph(Text("These estimates support an upper bound for integers whose number of distinct prime factors exceeds the second threshold. A matching lower bound is not established here."))),
                DescribeRole.Theorem))));
}
