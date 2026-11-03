using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma;

internal sealed class ThetaIntegratedReflectionGapDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integrated separation reserve for the complete physical theta kernel.",
        H("A positive first radial moment bounds the physical reflection gap"),
        Blocks(
            Paragraph(Text("Write Phi=romikPhi, p=(a+b)/2, d=|a-b|/2, "
                + "r0=p^2+d^2, and I_v,p(r)=cosh(2*v*sqrt(r-p^2))"
                + "*Phi(sqrt(r-p^2)+p)*Phi(sqrt(r-p^2)-p). "
                + "The full theta series and the entire unbounded integration domain are retained.")),
            Describe.Lean(
                DescribeId.Create("reflected-radial-moment"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap."
                    + "reflectedRadialMoment"),
                H("The reflected first excess moment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The reflected radial moment is the integral over "
                    + "r>r0 of (r-r0)*I_v,p(r). The definition imposes no truncation. "
                    + "Its positivity and genuine integrability under positive a,b and "
                    + "arbitrary real v are established along the proof of the next theorem."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("physical-kernel-integrated-gap"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/ThetaIntegratedReflectionGap."
                    + "physical_kernel_integrated_gap"),
                H("The curvature reserve survives complete integration"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For a,b>0 and every real v, the reflected radial moment is "
                        + "strictly positive, and a*b/24 times that moment is strictly less "
                        + "than physicalKernel(v,a,b)-physicalKernel(v,a,-b).")),
                    Paragraph(Text("The prior pointwise bound makes the nonnegative "
                        + "correction C(r)=a*b*(r-r0)*I_v,p(r)/6 smaller than the integrable "
                        + "difference I_v,d(r)-I_v,p(r) almost everywhere. Domination proves "
                        + "C and the first excess moment integrable. The remaining difference "
                        + "is positive on an interval of positive measure. The existing exact "
                        + "radial substitutions supply the factor 1/4, hence the constant 1/24. "
                        + "Evenness of cosh removes the nonnegative-weight restriction of "
                        + "the source pointwise estimate.")),
                    Paragraph(Text("The exceptional radial point r=2*p^2 is removed only "
                        + "as a Lebesgue null singleton. No pointwise claim is made there. "
                        + "This is an actual integrated bound with an explicit moment on its "
                        + "left side; no numerical estimate for that moment is asserted. "
                        + "The theorem compares individual kernel entries and does not establish "
                        + "matrix positive semidefiniteness or RH. Literature novelty is not claimed."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaGamma/ThetaReflectedQuantitativeGap")),
            DocumentEdge.Dependency.Create(
                GidRef.Create("D5/S3/Weil/ZetaGamma/ThetaReflectedKernelComparison"))
        ]));
}
