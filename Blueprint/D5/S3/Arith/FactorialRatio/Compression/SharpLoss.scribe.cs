using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FactorialRatio.Compression;

internal sealed class SharpLossDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FactorialRatio/Compression/SharpLoss.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Residue bands bound the large-prime compact excess, and a common parameter transfers bounded weights.",
        H("Primewise compact excess and shared budgets"),
        Blocks(
            Paragraph(Text(
                "Write G(r,s) for the gcd of the compact factorial products and "
                + "T(r,s)=tailLCM(rs+r-1,r-1). For r>=2 and s<r^2 the exact divisibility "
                + "T(r,s)|G(r,s) makes their quotient an integer. At a modulus q, the paired "
                + "floor sum subtracts r-1 from floor((rs+r-1)/q), truncated at zero. "
                + "The difference is nonnegative at every legal compact parameter.")),
            Describe.Lean(
                DescribeId.Create("compact-excess"),
                DeclarationHandle.Create(Prefix + "compactExcess"),
                H("The ordinary excess"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural r and s, compactExcess(r,s) is G(r,s) divided by T(r,s). "
                    + "Under r>=2 and s<r^2 this division is exact."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("floor-defect"),
                DeclarationHandle.Create(Prefix + "floorDefect"),
                H("The defect at one modulus"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural q,r,s,b, floorDefect(q,r,s,b) is the sum over "
                    + "0<=i<r of floor((i+1)b/q)+floor((s-ib)/q)-floor(b/q), "
                    + "minus max(floor((rs+r-1)/q)-(r-1),0), with natural subtraction. "
                    + "For q>=2, r>=1 and rb<=s the lower floor bound makes this "
                    + "the actual nonnegative integer difference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("local-prime-excess-bound"),
                DeclarationHandle.Create(Prefix + "local_prime_excess_bound"),
                H("The large-prime local bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For natural r,s,p,k with r>=2, s<r^2, p prime, r<p, "
                        + "1<=k and kp<=s, the exponent of p in compactExcess(r,s) "
                        + "is at most 2k+2r^2/(kp), interpreted as a real bound. "
                        + "Thus every integer k in the interval 1<=k<=floor(s/p) "
                        + "supplies a valid upper bound.")),
                    Paragraph(Text(
                        "Choose b=floor(kp/r). Then 0<b<p, rb<=s, and "
                        + "0<kp-rb<r. The strict lower inequality follows from "
                        + "coprimality of p and r and 0<k<r. The points ib, for "
                        + "1<=i<=r, occupy at most k quotient bands modulo p. "
                        + "Inside a fixed band, marks with residue at most u are "
                        + "separated by b, so there are at most floor(u/b)+1 marks.")),
                    Paragraph(Text(
                        "Put v=s mod p. If v+b<p, the floor sum equals "
                        + "r(floor(s/p)-1) plus the number of marks with residue at "
                        + "most v+b. The band count bounds its defect by 2k+r/b. "
                        + "If v+b>=p, the new marked interval has length v+b-p<b, "
                        + "so it contains at most one mark per band; the defect "
                        + "is at most 2k. Finally kp<=2rb gives r/b<=2r^2/(kp). "
                        + "Since s<p^2, higher powers of p contribute zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-prime-loss"),
                DeclarationHandle.Create(Prefix + "weightedPrimeLoss"),
                H("A common parameter across prime powers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural r,s,p,K and nonnegative integer weights c(j), "
                    + "weightedPrimeLoss is the minimum, over 0<=b<=floor(s/r), "
                    + "of the sum of c(j)floorDefect(p^j,r,s,b) for 1<=j<K. "
                    + "The same b is used in every summand. With unit weights "
                    + "and K=log_p(s)+1, this minimum equals the exponent of p "
                    + "in the ordinary excess when r>=2, s<r^2 and p is prime."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-excess"),
                DeclarationHandle.Create(Prefix + "weightedExcess"),
                H("A finite product of weighted prime losses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For natural r,s, a finite set P and nonnegative integer "
                    + "weights c(p,j), weightedExcess is the product over p in P "
                    + "of p raised to weightedPrimeLoss(r,s,p,log_p(s)+1,c(p,-)). "
                    + "For a weighted factorial model, identifying this product "
                    + "with its compact gcd divided by its full-composition gcd "
                    + "requires the corresponding primewise valuation formulas."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("weighted-shared-budget"),
                DeclarationHandle.Create(Prefix + "weighted_shared_budget"),
                H("A shared bound for two weight systems"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let r>=2, s<r^2 and let P be any finite set of primes. "
                        + "For natural C and natural weights c(p,j),d(p,j), assume "
                        + "c(p,j)+d(p,j)<=C for p in P and 1<=j<=log_p(s). "
                        + "Then weightedExcess(r,s,P,c) times weightedExcess(r,s,P,d) "
                        + "divides compactExcess(r,s)^C. Taking d=0 yields the "
                        + "bounded-weight divisibility for a single system.")),
                    Paragraph(Text(
                        "For each p, choose a parameter minimizing the unweighted "
                        + "sum of nonnegative defects. Evaluate both weighted sums "
                        + "at this same parameter. Their sum is at most C times "
                        + "the unweighted sum, while each separate minimum is at "
                        + "most its value there. This proves the inequality between "
                        + "exponents. Products over the finite prime set give the "
                        + "divisibility. The argument also covers C=0, empty P, "
                        + "and an empty interval of positive prime powers."))),
                DescribeRole.Theorem))));
}
