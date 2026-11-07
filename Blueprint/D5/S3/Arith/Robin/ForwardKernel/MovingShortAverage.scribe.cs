using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingShortAverageDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingShortAverage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaging a moving short increment gains the ratio of the short length to the averaging length.",
        H("Averaged moving short increments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("averaged-moving-increment-l2-bound"),
                DeclarationHandle.Create(Prefix + "averaged_moving_increment_l2_bound"),
                H("Uniform square-norm estimate for the moving average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and bounded on every compact interval. "
                        + "Fix 0<a<1 and 0<A<=B. Suppose M is eventually positive, "
                        + "X^a=O(M(X)), and M(X)=o(X). Assume that, for every fixed "
                        + "positive c1<=c2 and d, the cumulative variance of E at "
                        + "d*X is O(X*M(X)*log(X)), uniformly for increment lengths "
                        + "between c1*M(X) and c2*M(X). There is C>0 such that, "
                        + "for all sufficiently large X and every s in [0,1], "
                        + "the square norm on [A*X,B*X] of the M(X)-window average "
                        + "of E(x+s*x^a)-E(x) is at most "
                        + "C*(X^a/M(X))*sqrt(X*log(X))*sqrt(M(X)). "
                        + "Both C and the threshold are independent of s, and A=B is included.")),
                    Paragraph(Text(
                        "The comparable-length variance estimate is used at the scale M(X) in this statement. This is the corresponding generalization of Lemma 491.2, whose formulation also assumes the estimate at the short scale h.")),
                    Paragraph(Text(
                        "Write L(x)=s*x^a. Forward substitution separates M times "
                        + "the average into the integral of the fixed M-increment "
                        + "over [0,L(x)], a correction weighted by L'(x+r), "
                        + "and a terminal integral of length L(x+M)-L(x). "
                        + "On the enlarged spatial interval, L is at most H=C0*X^a, "
                        + "its derivative is at most H/X, and the terminal length "
                        + "is at most (H/X)*M<=H. Indicators place the capped "
                        + "integrals on fixed rectangles. Cauchy-Schwarz and Fubini "
                        + "then reduce their square norms to the comparable-length "
                        + "variance bound. Every endpoint map has derivative at "
                        + "least one, so the two-endpoint increment estimate applies. "
                        + "The sum of the three square bounds, followed by division "
                        + "by M, gives the stated gain."))),
                DescribeRole.Theorem))));
}
