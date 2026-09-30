using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FluidDynamics.Fourier;

internal sealed class PeriodicGradientInterpolationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FluidDynamics/Fourier/PeriodicGradientInterpolation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Periodic derivative fourth moments controlled by physical amplitude and second derivatives.",
        H("Periodic Gradient Interpolation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("periodic-gradient-interpolation-scalar"),
                DeclarationHandle.Create(Prefix + "periodic_deriv_fourth_moment"),
                H("Scalar periodic derivative estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For real a, b and M with a ≤ b and 0 ≤ M, let f, fp and fpp : ℝ → ℝ. Assume, for every real x, HasDerivAt f (fp x) x and HasDerivAt fp (fpp x) x, and assume fpp is continuous on all of ℝ. Assume f b = f a, fp b = fp a, and for every x ∈ Icc a b, |f x| ≤ M (the amplitudeIcc bound). Then the oriented interval integrals satisfy (∫ x in a..b, fp x ^ 4) ≤ 9 M² (∫ x in a..b, fpp x ^ 2). The statement is the scalar periodic physical-amplitude estimate; it does not assert a normalizedFourierH2 estimate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-gradient-interpolation-vector"),
                DeclarationHandle.Create(Prefix + "periodic_vector_gradient_fourth_moment"),
                H("Two-coordinate physical gradient estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For real a, b, M with a ≤ b and 0 ≤ M, let μ = volume.restrict (Ioc a b), so each coordinate is integrated over (a,b]. Let u, ux, uy, uxx and uyy : Fin 2 → ℝ → ℝ → ℝ, with all coordinates and all transverse variables ranging over ℝ. Assume, for every i : Fin 2 and every y, x ∈ ℝ, HasDerivAt (fun z => u i z y) (ux i x y) x and HasDerivAt (fun z => ux i z y) (uxx i x y) x; assume the analogous y-direction HasDerivAt statements for uy and uyy for every i, x and y. Assume uxx i is continuous as a function of x for every i and real y, and uyy i is continuous as a function of y for every i and real x. Assume for every real transverse coordinate the endpoint matches u i b y = u i a y and ux i b y = ux i a y, and u i x b = u i x a and uy i x b = uy i x a. Assume the amplitudeIcc² bound u 0 x y² + u 1 x y² ≤ M² for every x,y ∈ Icc a b.")),
                    Paragraph(Text("Assume, for every i, integrability on μ.prod μ of ux i ^ 4, uy i ^ 4, uxx i ^ 2 and uyy i ^ 2, and also integrability of the square of ux 0² + ux 1² + uy 0² + uy 1². Then the μ.prod μ integral of that squared gradient sum is at most 36 M² times the μ.prod μ integral of uxx 0² + uxx 1² + uyy 0² + uyy 1². The conclusion uses exactly the stated physical-amplitude and pure-second-derivative quantities; it does not identify this energy with normalizedFourierH2 or assert an H2 tensor-product boundary."))),
                DescribeRole.Theorem))));
}
