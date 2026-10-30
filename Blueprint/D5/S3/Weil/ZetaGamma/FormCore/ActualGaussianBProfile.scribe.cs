using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualGaussianBProfileDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Evaluate the original complete theta transform and actual even B image "
            + "of the same literal physical Gaussian source.",
        H("The actual Gaussian source and its even B image"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-gaussian-suzuki-even-b"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaGamma/FormCore/ActualGaussianBProfile."
                    + "actual_gaussian_suzuki_evenB"),
                H("Complete source identification with convergent tails"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For each nonnegative site a, take the original physical source "
                        + "F(x)=exp(9a/2-exp(2a)x). Its actual Gamma profile is integrable, "
                        + "and every translated exp(-5s/4)-weighted right-tail integrand "
                        + "at t at least zero is integrable. The actual even B profile "
                        + "is exactly cPhi*Phi(a+|r|), with cPhi=pi^(1/4)/4 and the "
                        + "original factor two in the even-B definition.")),
                    Paragraph(Text(
                        "The complete theta series is evaluated by an actual HasSum "
                        + "calculation, including every positive theta mode. The right "
                        + "tail is then evaluated by a differentiable primitive whose "
                        + "weighted value tends to zero at infinity. Existing complete "
                        + "theta-jet bounds pay integrability and the endpoint. No "
                        + "linearity of the B map or profile identity is assumed.")),
                    Paragraph(Text(
                        "This repository-derived source calculation supplies the "
                        + "normalization and actual source match for compact theta-cusp "
                        + "approximation. It does not infer a logarithmic Gamma form "
                        + "domain from H6 alone, extend a theorem to all of V, assert "
                        + "a noncompact signed Weil formula, or prove RH."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Fourier/ThetaCuspConvolutionRegularity")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Analytic/Fourier/XiThetaTransform"))
        ]));
}
