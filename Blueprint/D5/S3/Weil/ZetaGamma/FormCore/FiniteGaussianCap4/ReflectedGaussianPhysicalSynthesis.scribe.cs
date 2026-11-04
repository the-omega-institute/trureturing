using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class ReflectedGaussianPhysicalSynthesisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual reflected Gaussian physical synthesis",
        H("Actual reflected Gaussian physical synthesis"),
        Blocks(
            Paragraph(Text("The actual reflected Gaussian coefficient core and the continuous weighted synthesis are now connected as functions. The same coefficient curve f retains its proved closed-span identity with the actual central-charge kernel. Its graph and absolute Mellin representatives are the normalized reflected Gaussian on the positive half-line.")),
            Describe.Lean(
                DescribeId.Create("actual-reflected-gaussian-physical-synthesis"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianPhysicalSynthesis.actual_reflected_gaussian_physical_synthesis"),
                H("The actual core synthesizes the actual Gaussian"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every 0<t<1/36, write a=positiveGaussianSite(t). Both coordinates of synthesis(f(t)) equal gaussianFeature(reflectedSourceCoefficient,reflectedSourceSite(a))/(2 gaussianSiteAmplitude(a)) almost everywhere for their respective measures: (x^(7/2)+x^(15/2)) dx on x>0 and x^(5/4) dx on x>0. The existing Gaussian generating series is even under reflection; reindexing it by n=2k gives the pointwise series with exactly the weighted coefficients of f(t). The synthesis partial sums converge in each Lp space. A subsequence converges almost everywhere, and uniqueness of its pointwise limit identifies the representatives. This reuses the original finite synthesis and its literal representatives; it does not posit a physical realization.")),
                    Paragraph(Text("This result supplies the actual coefficient-to-function bridge for the constructed central-charge core. It does not identify that charge with the original H6 full-line mu, prove original-domain surjectivity, establish a closed synthesis image, or resolve RH. The inherited Laguerre polynomial source retains its upstream OpenAI/math attribution and Apache-2.0 notice. This source-relative synthesis theorem makes no literature-priority claim."))),
                DescribeRole.Theorem))));
}
