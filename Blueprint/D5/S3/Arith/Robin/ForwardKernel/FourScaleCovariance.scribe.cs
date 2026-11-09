using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourScaleCovarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourScaleCovariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Four separated variance scales control the covariance of moving increments uniformly on subintervals.",
        H("Four-scale separation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-mem-lp"),
                DeclarationHandle.Create(Prefix + "moving_memLp"),
                H("Square integrability of moving increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If E is locally bounded and measurable and a>0, then x maps to E(x+s*x^a)-E(x) belongs to L2 on every finite interval (l,r], for every real s."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("average-mem-lp"),
                DeclarationHandle.Create(Prefix + "average_memLp"),
                H("Square integrability of averaged moving increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For locally bounded measurable E and a>0, the window average of x maps to E(x+s*x^a)-E(x) belongs to L2 on every finite interval (l,r], for all real s and window lengths M. Local integrability makes the window average continuous."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("covariance-of-norm-bounds"),
                DeclarationHandle.Create(Prefix + "covariance_of_norm_bounds"),
                H("Averaging and translation bounds control covariance"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let f and z be locally square integrable and let M>0. Suppose translated L2 norms of f are bounded by F, the L2 norm of z by Z, the L2 norm of the window average of f by U, the translation difference of z by D, and endpoint-strip norms of f and z by F and S. Under joint integrability of the translated pairing, the absolute integral of f*z over [l,r] is at most U*Z+F*D+2*F*S."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-scale-covariance-bound"),
                DeclarationHandle.Create(Prefix + "four_scale_covariance_bound"),
                H("Uniform covariance bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be locally bounded and measurable, 0<a<b<1, "
                        + "h=X^a and k=X^b. Suppose h, M, T and k satisfy the "
                        + "comparable-length cumulative-variance upper bound, "
                        + "with h=O(M), M=O(T), and T=O(k). There is C>0 such "
                        + "that, eventually in X, simultaneously for all s,t in "
                        + "[0,1] and X<=l<=r<=2*X, the absolute integral of "
                        + "(E(x+s*x^a)-E(x))*(E(x+t*x^b)-E(x)) over [l,r] "
                        + "is at most C*X*log(X)*sqrt(h*k) times "
                        + "sqrt(h/M)+sqrt(M/T)+sqrt(T/k).")),
                    Paragraph(Text(
                        "Average the short moving increment over a window M. "
                        + "MovingShortAverage.averaged_moving_increment_l2_bound "
                        + "bounds its pairing with the long increment. "
                        + "AveragingBounds.windowAverage_pairing_eq writes the "
                        + "remaining difference as an average of translated "
                        + "pairings. Interval additivity separates each translation "
                        + "into a translation difference and the two intervals "
                        + "[l,l+v] and [r,r+v]. TranslationStripBounds supplies "
                        + "the translation norm and short-strip square estimates. "
                        + "All translated intervals lie inside [X,3*X]; their "
                        + "norms are bounded on this larger interval. The same "
                        + "identity applies when l=r or r-l<M, since it requires "
                        + "no nonempty overlap."))),
                DescribeRole.Theorem))));
}
