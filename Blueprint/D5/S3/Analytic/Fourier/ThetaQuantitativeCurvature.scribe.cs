using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class ThetaQuantitativeCurvatureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An explicit quadratic reserve in the square-variable logarithm of the complete theta kernel.",
        H("Quantitative concavity of the complete theta kernel"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-square-strong-concavity"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/ThetaQuantitativeCurvature."
                    + "actual_square_strong_concavity"),
                H("Strict concavity after adding the quadratic correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For the literal complete theta kernel Phi=romikPhi, the function "
                        + "r maps to log(Phi(sqrt(r)))+r^2/48 is strictly concave on r>0. "
                        + "The correction has the displayed fixed coefficient and is retained in "
                        + "the conclusion; no concavity assumption is introduced.")),
                    Paragraph(Text("The proof reuses the full infinite-tail estimate in "
                        + "ThetaRadialCurvature without dropping its negative reserve. With "
                        + "y=pi*exp(2*x), the normalized fourth logarithmic numerator is at most "
                        + "-(12623/64000) times the positive first-mode reserve. For x>=0, "
                        + "the fourth derivative of log(Phi(x)) is at most -y/6, which is "
                        + "strictly below -1/2. Thus the fourth derivative of "
                        + "log(Phi(x))+x^4/48 is negative. Its odd origin jets vanish, and "
                        + "the square-variable derivative argument gives the stated strict concavity.")),
                    Paragraph(Text("The complete theta series, all tail modes and the entire "
                        + "positive ray remain in scope. The immediate consumer is the explicit "
                        + "pointwise reflected-integrand gap in ThetaReflectedQuantitativeGap. "
                        + "This is a repository derivation from the existing analytic reserve; "
                        + "no literature-priority claim or RH conclusion is asserted."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Fourier/ThetaRadialCurvature"))
        ]));
}
