using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer.FiniteSieve;

internal sealed class SieveFourierAdmissibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/FiniteSieve/SieveFourierAdmissibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positively shifted smooth interval averages are admissible real Fourier weights.",
        H("Smooth interval Fourier weights"),
        Blocks(
            Paragraph(Text(
                "For delta>0, let rho be the unit-mass smooth bump centered at "
                + "2*delta and supported in [delta,3*delta]. The weight "
                + "smoothedInterval(delta,a,b)(x) averages the indicator of "
                + "(a+r,b+r] against rho(r). It is exactly the convolution of "
                + "rho with the indicator of (a,b]. A smooth compactly "
                + "supported convolution kernel makes this convolution smooth.")),
            Describe.Lean(
                DescribeId.Create("smooth-interval-admissible"),
                DeclarationHandle.Create(Prefix + "smooth_interval_admissible"),
                H("Admissibility of the shifted interval average"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For delta>0 and 0<=a<=b, the real weight "
                        + "smoothedInterval(delta,a,b) is infinitely differentiable "
                        + "and has compact support contained in (0,infinity). "
                        + "There is a nonnegative constant C such that its Fourier "
                        + "transform has norm at most C/xi^2 whenever |xi|>=1.")),
                    Paragraph(Text(
                        "The support lies in [a+delta,b+3*delta], whose lower "
                        + "endpoint is positive. Complexifying the smooth compact "
                        + "weight gives a Schwartz function. Its Mathlib Fourier "
                        + "transform is also Schwartz, and its order-two seminorm "
                        + "bounds xi^2 times the norm of the transform. "
                        + "The integral convention is checked directly: the "
                        + "phase is exp(-2*pi*I*x*xi), with Lebesgue measure and "
                        + "no extra normalizing factor. The constant may depend "
                        + "on delta and the interval endpoints; it is independent "
                        + "of the modulus and sampling scale. The empty interval "
                        + "a=b is included."))),
                DescribeRole.Theorem))));
}
