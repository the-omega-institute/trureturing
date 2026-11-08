using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FourthMomentInterfaceBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FourthMomentInterfaceBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fourth-moment estimates on an exponent band bound normalized moving increments under logarithmic dyadic sampling.",
        H("The fourth-moment interface bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("fourth-moment-bound-interface"),
                DeclarationHandle.Create(Prefix + "fourth_moment_bound_interface"),
                H("Uniform fourth absolute moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and bounded on compact intervals, "
                        + "with 0<alpha<theta<beta<1. Assume the uniform fixed-increment "
                        + "fourth-moment bound on the exponent band [alpha,beta], with "
                        + "nonnegative constant C4. There is C>=0 such that, for all "
                        + "sufficiently large X and every s in [0,1], the fourth absolute "
                        + "moment of (E(x+s*x^theta)-E(x))/sqrt(x^theta*log(x)) "
                        + "under dx/(x*log(2)) on [X,2X] is at most C.")),
                    Paragraph(Text(
                        "The moving-increment estimate bounds the unnormalized integral "
                        + "by K*C4*X*(X^theta)^2*log(X)^2, with K depending only on "
                        + "the exponent band. On [X,2X], both x>=X and "
                        + "x^theta*log(x)>=X^theta*log(X). Dividing by these lower "
                        + "bounds and by log(2) gives C=(K/log(2))*C4. "
                        + "Continuous moving steps and compact boundedness of E give "
                        + "the integrability needed for comparison."))),
                DescribeRole.Theorem))));
}
