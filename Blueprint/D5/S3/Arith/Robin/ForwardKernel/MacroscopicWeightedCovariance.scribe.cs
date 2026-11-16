using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MacroscopicWeightedCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MacroscopicWeightedCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Freezing and fixed block limits give the weighted overlap covariance of macroscopic lengths.",
        H("Covariance of frozen macroscopic lengths"),
        Blocks(
            Paragraph(Text(
                "Let E be measurable and bounded on every compact interval, with "
                + "D_v(x)=E(x+v)-E(x). Assume 0<alpha<theta<beta<1 and that "
                + "V(Y,v)/(Y*v*log(Y/v)) tends uniformly to one for "
                + "Y^alpha<=v<=Y^beta. Set h=X^theta, N=X*h*log(X), "
                + "kappa=1-theta, u_j=1+j/n and I_j=[u_j*X,u_(j+1)*X], "
                + "where n is a fixed positive integer. The length values a(u_j) "
                + "and b(u_j) lie in [0,M] for some M>0; w(u_j) are arbitrary real weights. "
                + "Only these finitely many values are used, so no continuity is required.")),
            Describe.Lean(
                DescribeId.Create("fixed-block-covariance-tendsto"),
                DeclarationHandle.Create(Prefix + "fixed_block_covariance_tendsto"),
                H("Weighted covariance on fixed blocks"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "As X tends to infinity, the sum over j<n of w(u_j) times "
                        + "the integral on I_j of D_(h*a(u_j))*D_(h*b(u_j)), divided by N, "
                        + "tends to (kappa/n) times the sum of w(u_j)*min(a(u_j),b(u_j)).")),
                    Paragraph(Text(
                        "Apply fixed_length_covariance_tendsto with the common length "
                        + "M*X^theta and parameters a(u_j)/M and b(u_j)/M in [0,1]. "
                        + "The ratio of its normalizer X*(M*X^theta)*log(X/(M*X^theta)) "
                        + "to N tends to M*kappa. Since each block has macroscopic "
                        + "length 1/n, multiplication by this ratio and finite summation "
                        + "give the stated limit. The fixed-length theorem includes "
                        + "zero parameters, so zero lengths require no separate argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-block-square-tendsto"),
                DeclarationHandle.Create(Prefix + "fixed_block_square_tendsto"),
                H("Frozen squared norms"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sum over j<n of the integrals on I_j of D_(h*a(u_j))^2, "
                    + "divided by N, tends to (kappa/n) times the sum of a(u_j). "
                    + "This is the weighted covariance limit with b=a and all weights equal to one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("fixed-block-square-limit-mem"),
                DeclarationHandle.Create(Prefix + "fixed_block_square_limit_mem"),
                H("Size of the squared norm limit"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every frozen length lies in [0,M], then (kappa/n) times "
                    + "their sum lies in [0,M]. Indeed, 0<kappa<1 and the sum "
                    + "of n such lengths lies between zero and n*M."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("young-abs"),
                DeclarationHandle.Create(Prefix + "young_abs"),
                H("A weighted product bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real x and y and every positive r, |x*y| is at most x^2/r+r*y^2. "
                    + "The elementary quadratic inequality controls both freezing errors "
                    + "and changes in the two time parameters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("weighted-covariance-tendsto"),
                DeclarationHandle.Create(Prefix + "weighted_covariance_tendsto"),
                H("Continuous macroscopic weights and lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonnegative C1 functions a and b on [1,2] and a real continuous "
                        + "weight w, the integral of w(x/X)*D_(X^theta*a(x/X))(x)"
                        + "*D_(X^theta*b(x/X))(x), divided by X*X^theta*log(X), "
                        + "tends to kappa times the integral of w(u)*min(a(u),b(u)) on [1,2].")),
                    Paragraph(Text(
                        "Compactness supplies common length and derivative bounds M and L. "
                        + "On n equal blocks freeze a, b and w at the left endpoints. "
                        + "The difference of the weighted products splits into the weight error "
                        + "and the two freezing errors. Young's inequality bounds their block "
                        + "integrals by the squared freezing errors and squared increment norms. "
                        + "The uniform bound 880*M controls the moving norms, while the fixed "
                        + "block square limit controls the frozen norm. Uniform continuity "
                        + "controls the weight error and the overlap Riemann sum. For each "
                        + "positive tolerance choose n once, then let X tend to infinity; "
                        + "the proof does not choose n as a function of X."))),
                DescribeRole.Theorem))));
}
