using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Weighted;

internal sealed class CompactBudgetDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Weighted/CompactBudget.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual weighted compact products share the ordinary compact compression budget.",
        H("Weighted compact products and their exact excess"),
        Blocks(
            Paragraph(Text(
                "Let r>=2 and H=rs+r-1. The legal parameter family is 0<=b<=floor(s/r). "
                + "For nonnegative integer weights c(p,j), with j>=1 denoting p^j, "
                + "write B(n) for the weighted factorial with cutoff H. The actual compact "
                + "product at b is the product over 0<=i<r of B((i+1)b)/B(b) times B(s-ib). "
                + "Every quotient is an integer because weighted factorials increase in divisibility.")),
            Describe.Lean(
                DescribeId.Create("compact-weighted-product"),
                DeclarationHandle.Create(Prefix + "compactWeightedProduct"),
                H("One common compact parameter"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "compactWeightedProduct is the actual product of weightedValue quotients "
                    + "and weightedValue factors, with one and the same b throughout. The "
                    + "adapter shiftedWeights sends the zero-based coefficient at index j "
                    + "in CompositionGcd to the coefficient c(p,j+1). Thus c(p,1) weights "
                    + "division by p, and the unused index c(p,0) has no effect."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-weighted-excess"),
                DeclarationHandle.Create(Prefix + "compactWeightedExcess"),
                H("The actual gcd quotient"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let G_B be the gcd of the actual compact products over all legal b, "
                    + "and let T_B be weightedTail(H,r-1,shiftedWeights(c)). The exact "
                    + "weighted composition theorem identifies T_B with the gcd over all "
                    + "r-part compositions of rs. The floor lower bounds prove T_B divides "
                    + "every compact term, so compactWeightedExcess is the exact positive "
                    + "integer E_B=G_B/T_B. This includes s=0 and the zero weight system."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compact-weighted-excess-factorization"),
                DeclarationHandle.Create(Prefix + "compactWeightedExcess_factorization"),
                H("Exact primewise exponents"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r>=2, any s, any natural weight system c and any p in primesLE(H), "
                    + "the exponent of p in E_B equals weightedPrimeLoss(r,s,p,log_p(s)+1,c(p,-)). "
                    + "The product valuation is the weighted sum of the paired floor sums. "
                    + "Subtracting the tail valuation gives the weighted sum of nonnegative "
                    + "floor defects. Powers above s contribute zero at every legal b. "
                    + "Taking the gcd takes the minimum over b of that whole sum, without "
                    + "choosing a different b for each prime power."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-weighted-excess-euler-product"),
                DeclarationHandle.Create(Prefix + "compactWeightedExcess_eq_weightedExcess"),
                H("Identification with the defect product"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r>=2 and all s,c, the actual quotient E_B is exactly "
                    + "weightedExcess(r,s,primesLE(H),c). Primes outside this finite set "
                    + "have exponent zero in every compact weighted term, hence also in its gcd "
                    + "and exact quotient. Equality of all prime exponents gives the integer identity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-weighted-shared-budget"),
                DeclarationHandle.Create(Prefix + "actual_weighted_shared_budget"),
                H("A shared budget for two actual weighted families"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r>=2, s<r^2 and C>=0, suppose c(p,j)+d(p,j)<=C for every "
                    + "p in primesLE(H) and 1<=j<=log_p(s). The actual quotients E_c and E_d "
                    + "then satisfy E_c E_d | E^C, where E is the ordinary factorial compact "
                    + "excess for the same r,s and the same legal parameter family. The primewise "
                    + "argument evaluates both weighted costs at a single parameter minimizing "
                    + "the ordinary cost; separate weighted minimizers are never identified."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-weighted-budget"),
                DeclarationHandle.Create(Prefix + "actual_weighted_budget"),
                H("The bounded-weight budget"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For r>=2 and s<r^2, if c(p,j)<=C on the same finite prime-power range, "
                    + "then the actual weighted compact excess E_c divides E^C. The zero system "
                    + "is the second family in the shared-budget theorem. No extra realization "
                    + "hypothesis or assumed valuation formula appears in this statement."))),
                DescribeRole.Theorem))));
}
