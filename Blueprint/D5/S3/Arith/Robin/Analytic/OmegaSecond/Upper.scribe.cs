using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.Analytic.OmegaSecond;

internal sealed class UpperDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Rankin reduction and the optimized prime budget for the second distinct-prime threshold.",
        H("Second-threshold Rankin upper estimate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("second-scale"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale"),
                H("Second-threshold counting scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scale is log(x)/(log(log(x))*sqrt(log(log(x)))), equal to log(x)/(log(log(x)))^(3/2) for sufficiently large x."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("saddle"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle"),
                H("Explicit saddle parameter"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the prime cutoff P, the saddle parameter is pi*sqrt(log(P))/(2*sqrt(3)). It grows with the cutoff."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("euler-cost"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.eulerCost"),
                H("Fixed inverse Euler cost"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The fixed cost is the logarithm of one plus the sum over natural n of n^(-2). It bounds the unweighted inverse Euler factors for every Rankin parameter at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("rankin-reduction"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.rankin_reduction"),
                H("Exact second-threshold Rankin reduction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real x greater than exp(1) and every real s at least two, tailCount(1,x) is at most exp(s*budget(log(x))+remainder(log(x),s,x)+eulerCost). The finite count includes precisely the integers 1<=n<=x whose number of distinct prime divisors strictly exceeds log(x)/log(log(x))+log(x)/(log(log(x)))^2.")),
                    Paragraph(Text("The prime cutoff is exactly log(x). The finite Euler product, localized weight decomposition and threshold cancellation retain the same integer count and real endpoint throughout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-scale-top"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.secondScale_top"),
                H("Divergence of the finer scale"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The second-threshold scale tends to positive infinity as x tends to positive infinity. A fixed additive Euler cost therefore vanishes after division by this scale."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("saddle-budget-limit"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.saddle_budget_limit"),
                H("Budget contribution at the saddle"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The product saddle(P)*budget(P), divided by P/(log(P)*sqrt(log(P))), tends to pi/sqrt(3). The coefficient two in the exact prime budget combines with the explicit saddle constant.")),
                    Paragraph(Text("This stage concerns an upper bound at the second distinct-prime threshold. A matching lower bound has not been established."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/Analytic/OmegaSecond/Upper.result"),
                H("Explicit second-threshold upper coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every real epsilon>0, all sufficiently large real x satisfy tailCount(1,x)<=exp((2*pi/sqrt(3)+epsilon)*log(x)/(log(log(x)))^(3/2)). The strict second threshold and the range 1<=n<=x are exactly those of tailCount(1,x).")),
                    Paragraph(Text("At the explicit saddle, the prime budget has limiting coefficient pi/sqrt(3), and the localized remainder has upper coefficient pi/sqrt(3) on the finer scale. The fixed Euler cost vanishes there. This is an upper bound only; a matching lower bound remains unproved."))),
                DescribeRole.Theorem))));
}
