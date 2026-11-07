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
                    "Let E be Borel measurable and locally bounded, and assume the cumulative variance asymptotic uniformly in the band Y^alpha<=u<=Y^beta, where 0<alpha<theta<beta<1. There is C>0 and one threshold for X such that every s in [0,1] satisfies integral_X^(2X) D_(s*x^theta)(x)^2 dx<=C*X*X^theta*log(X). Put h=X^theta and L=s*x^theta. Average D_L(x)=D_v(x)-D_(v-L)(x+L) over v in [3h,4h]. The first square is bounded by comparable-length cumulative variance. Translate the second integration variable to w=v-L and enlarge to [h,4h]. Fubini and the substitution y=x+s*x^theta, whose derivative is at least one, bound its x-integral by V(3X,w). This substitution applies to measurable integrands, so no continuity assumption on E is needed. All length and image bounds hold at one threshold independently of s."))),
                DescribeRole.Theorem))));
}
