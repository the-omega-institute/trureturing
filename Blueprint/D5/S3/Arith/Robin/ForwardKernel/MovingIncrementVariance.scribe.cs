using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MovingIncrementVarianceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MovingIncrementVariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Averaging comparable increments gives a bound uniform over moving increment parameters.",
        H("MovingIncrementVariance"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("moving-increment-square-bound"),
                DeclarationHandle.Create(Prefix + "moving_increment_square_bound"),
                H("Uniform moving-increment bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let E be Borel measurable and locally bounded, and assume the cumulative variance asymptotic uniformly in the band Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. There is C>0 and one threshold for X such that every s in [0,1] satisfies integral_X^(2X) D_(s*x^theta)(x)^2 dx<=C*X*X^theta*log(X). Apply the two-endpoint square estimate with p(x)=x, q(x)=x+s*x^theta, R=X^theta, C0=2, m=1, and Y=3X. The comparable-length variance estimate supplies a common bound for R<=u<=4R. The moving endpoint has derivative 1+s*theta*x^(theta-1)>=1; its gap is at most 2R and its image lies in [1,3X]. The estimate applies to measurable locally bounded E. All length and image bounds hold at one threshold independently of s."))),
                DescribeRole.Theorem))));
}
