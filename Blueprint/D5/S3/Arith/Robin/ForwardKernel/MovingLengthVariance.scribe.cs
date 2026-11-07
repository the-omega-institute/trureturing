using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingLengthVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingLengthVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform band variance controls comparable and shorter increment lengths.",
        H("MovingLengthVariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("comparable-length-variance-bound"),
                DeclarationHandle.Create(Prefix + "comparable_length_variance_bound"),
                H("Comparable increment lengths"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be Borel measurable and locally bounded, with cumulative variance asymptotic to Y*u*log(Y/u) uniformly for Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. For fixed 0<A<=B and d>0 there is C>0 such that, for all sufficiently large X and all A*X^theta<=u<=B*X^theta, V(d*X,u)<=C*X*X^theta*log(X). Both ends of this entire length interval enter the exponent band at one threshold."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("shorter-increment-square-bound"),
                DeclarationHandle.Create(Prefix + "shorter_increment_square_bound"),
                H("All shorter increments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same hypotheses, for every c>0 there is C>0 such that, for all sufficiently large X and every 0<=u<=h=c*X^theta, the integral of D_u(x)^2 over [X,2X] is at most C*X*h*log(X/h). Apply the two-endpoint square estimate with p(x)=x, q(x)=x+u, R=h, C0=1, and m=1. The comparable-length estimate controls V(3X,v) uniformly for h<=v<=3h, and log(X/h)=(1-theta)*log(X)-log(c)."))),
                DescribeRole.Theorem))));
}
