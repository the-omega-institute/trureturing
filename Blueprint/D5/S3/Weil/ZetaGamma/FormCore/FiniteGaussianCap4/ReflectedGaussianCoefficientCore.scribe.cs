using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore.FiniteGaussianCap4;

internal sealed class ReflectedGaussianCoefficientCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual three-point reflected Gaussian sources generate the weighted central-charge coefficient kernel.",
        H("The actual reflected Gaussian coefficient core"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-reflected-gaussian-coefficient-core"),
            DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/FiniteGaussianCap4/ReflectedGaussianCoefficientCore.actual_reflected_gaussian_coefficient_core"),
            H("The literal source [1,1,-2] at [a,-a,0]"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Put z(n)=normalizedCentralMellin(2n)/normalizedCentralMellin(0), N(n)=centralNormalization(n), a(t)=log((1+sqrt(t))/(1-sqrt(t)))/2. Let d(t,n) be the repository's actual finiteGaussianNormalizedCoefficient of the source [1,1,-2] at [a(t),-a(t),0], evaluated at 2n and divided by 2*gaussianSiteAmplitude(a(t)). On 0<t<1/36 these coefficients have a genuine l2 carrier f(t,n)=(n+1)^2*d(t,n), and their closed real span is exactly ker inner(z(n)/(n+1)^2, -).")),
                Paragraph(Text("The actual normalization recurrence supplies inverse coefficient growth; the existing central Mellin weight recurrence gives |z(n)|<=1. The existing atom reflection formulas give d(t,n)=t^n/N(2n) for n>=1, and the actual finite-source central mass HasSum fixes coordinate zero. This proof does not assume a Gaussian expansion, density, or Laguerre completeness. Physical synthesis, continuity of the required energy forms, and identification with any original Suzuki admissible domain remain separate obligations; no RH statement is concluded."))),
            DescribeRole.Theorem))));
}
