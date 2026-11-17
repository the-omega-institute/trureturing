using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class MomentInterfaceBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/MomentInterfaceBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even-moment increment estimates give uniform normalized moments under logarithmic dyadic sampling.",
        H("Normalized even-moment bounds"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-even-moment-bound"),
                DeclarationHandle.Create(Prefix + "normalized_even_moment_bound"),
                H("Normalization of a raw even moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and bounded on compact intervals, "
                        + "theta>=0, K>=0, and m a natural number. Suppose that for "
                        + "all sufficiently large X, uniformly for s in [0,1], "
                        + "the integral of |E(x+s*x^theta)-E(x)|^(2*m) over [X,2X] "
                        + "is at most K*X*(X^theta*log(X))^m. Then the 2*m-th "
                        + "absolute moment of (E(x+s*x^theta)-E(x))/sqrt(x^theta*log(x)) "
                        + "under dx/(x*log(2)) on [X,2X] is eventually at most "
                        + "K/log(2), uniformly for s in [0,1]. The conclusion also "
                        + "includes m=0 and theta=0.")),
                    Paragraph(Text(
                        "For X>1 and x in [X,2X], the inequalities x>=X and "
                        + "x^theta*log(x)>=X^theta*log(X)>0 bound the full "
                        + "denominator below by X*(X^theta*log(X))^m. "
                        + "Local boundedness and measurability of E along continuous "
                        + "moving endpoints give compact integrability, permitting "
                        + "integration of this comparison. The raw bound "
                        + "cancels the scale, leaving only the probability density "
                        + "factor 1/log(2)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-moment-bound-interface"),
                DeclarationHandle.Create(Prefix + "second_moment_bound_interface"),
                H("Uniform second absolute moments"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let E be Borel measurable and bounded on compact intervals, "
                        + "with 0<alpha<theta<beta<1, and assume the cumulative "
                        + "variance asymptotic on [alpha,beta]. There exists C>=0 "
                        + "such that for every sufficiently large X and every "
                        + "s in [0,1], the second absolute moment of the normalized "
                        + "increment under logarithmic dyadic sampling is at most C.")),
                    Paragraph(Text(
                        "The uniform moving-increment square estimate gives a raw "
                        + "bound K*X*X^theta*log(X). Applying the even-moment "
                        + "normalization with m=1 yields C=K/log(2)."))),
                DescribeRole.Theorem))));
}
