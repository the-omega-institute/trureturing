using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;

internal sealed class BinaryLogJumpCountermodelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact binary log-jump count",
        H("Sharpness of the power one sixth"),
        Blocks(
            Definition("continuum-count", "count", "Oscillatory continuum count",
                "With v=x^(1/6), the count is x−x^(1/2)+(1/3)x^(2/3)sin(v)−(1/6)x^(5/6)cos(v)."),
            Definition("log-count", "logCount", "Log-weighted count at a real cutoff",
                "For coefficients c indexed by natural numbers, sum log(n)c(n) from 0 to floorNat(x), "
                + "including the upper endpoint."),
            Definition("tail-kernel", "roundedTailKernel", "Kernel of the rounded count",
                "At x the kernel is (logCount(c,x)−x)/x². Its actual tail q(x) is the integral "
                + "of this kernel over (x,∞)."),
            Definition("signed-mass", "roundedSignedMass", "Signed weighted window mass",
                "Integrate q(x)/√x over the window."),
            Definition("negative-mass", "roundedNegativeMass", "Negative weighted window mass",
                "Integrate max(−q(x),0)/√x over the window."),
            Describe.Lean(
                DescribeId.Create("rounded-window-obstruction"),
                Handle("roundedWindowObstruction"),
                H("A binary count with bounded centering and power growth of negative mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "There exist coefficients c(n) in {0,1}, all zero through 8, and a real C ≥ 0. "
                        + "At every consecutive pair n,n+1 the increment of the count is log(n+1)c(n+1). "
                        + "At every real x ≥ 8 its distance from the continuum count F is at most "
                        + "|F(8)|+4 log(x), and its tail kernel is integrable above x. "
                        + "The ratio of the rounded count to x tends to one.")),
                    Paragraph(Text(
                        "On every real interval [a,b] with 8 ≤ a ≤ b, the signed mass centered by "
                        + "adding 2 log(b/a) has absolute value at most C. The negative mass is at least "
                        + "(3/2)(b^(1/6)−a^(1/6))−C. For every real p>1, the negative mass on [Y,Y^p] is "
                        + "eventually at least (1/4)Y^(p/6).")),
                    Paragraph(Text(
                        "The continuum tail is −2x^(−1/2)+x^(−1/3)sin(x^(1/6)). Its weighted signed "
                        + "primitive is −2 log(x)−6 cos(x^(1/6)). A trigonometric lower bound on "
                        + "its weighted negative part gives a primitive with leading term (3/2)x^(1/6).")),
                    Paragraph(Text(
                        "Take floor increments of the integral of F′(t)/log(t) from 8. This density "
                        + "lies between zero and one. Discrete Abel summation and continuous integration "
                        + "by parts give the logarithmic error at every real cutoff x≥8. The resulting weighted "
                        + "tail error is bounded by an integrable multiple of x^(−5/4). Its total integral "
                        + "bounds the error in both window estimates, since q ↦ max(−q,0) is 1-Lipschitz.")),
                    Paragraph(Text(
                        "The eventual lower bound on [Y,Y^p] rules out any smaller uniform power "
                        + "for the negative mass under the monotonicity and signed-primitive assumptions. "
                        + "The coefficients select an unrestricted subset of integers. Its count is nondecreasing because each term is nonnegative. With cutoff 8 and centering 2 it satisfies the hypotheses of the monotone-count upper bound."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) =>
        DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/BinaryLogJumpCountermodel." + name);

    private static DocumentBlock Definition(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id), Handle(name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
