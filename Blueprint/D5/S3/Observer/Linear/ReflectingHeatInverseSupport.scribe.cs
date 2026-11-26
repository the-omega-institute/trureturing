using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Linear;

internal sealed class ReflectingHeatInverseSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflecting heat interpolant has a centered inverse density with the prescribed exponential moments.",
        H("Inverse Fourier support of the reflecting heat interpolant"),
        Blocks(Describe.Lean(
            DescribeId.Create("reflecting-heat-interpolant-inverse-support"),
            DeclarationHandle.Create("D5/S3/Observer/Linear/ReflectingHeatInverseSupport.momentInterpolant_inverse_support"),
            H("Centered density and reflecting mode moments"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For an entire multiplier with the prescribed radial half-width L/2 and "
                    + "the real-axis Joukowski bound, the reflecting heat interpolant satisfies "
                    + "the directional bound of order n minus two plus m and has a square-integrable "
                    + "real restriction. The inverse Fourier support theorem gives an integrable "
                    + "representative of its inverse L2 class, vanishing at every point outside "
                    + "the centered interval of length L.")),
                Paragraph(Text(
                    "The transform of this density with angular kernel exp(-i z t) is entire "
                    + "by differentiation under the integral. Classical Fourier agreement on "
                    + "the real axis and the identity theorem recover the interpolant on the "
                    + "whole plane. At the node minus i times the reflecting rate, the kernel "
                    + "becomes the corresponding real decaying exponential. The moment is zero "
                    + "off the target mode and equals the nodal derivative times the multiplier "
                    + "at the target node on that mode."))),
            DescribeRole.Theorem))));
}
