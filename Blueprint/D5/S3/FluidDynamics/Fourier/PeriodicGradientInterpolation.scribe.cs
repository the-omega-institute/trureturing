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
                Blocks(Paragraph(Text("Let a and b be real endpoints with a at most b, and let M be nonnegative. Let f, fp and fpp be real functions on the line. Assume f has derivative fp everywhere, fp has derivative fpp everywhere, and fpp is continuous. Assume f and fp take equal values at a and b, and the absolute value of f is at most M throughout the closed interval. Then the interval integral of the fourth power of fp is at most nine times M squared times the interval integral of the square of fpp. The proof integrates the derivative of f times the cube of fp, cancels the periodic endpoint term, and applies a pointwise square inequality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("periodic-gradient-interpolation-vector"),
                DeclarationHandle.Create(Prefix + "periodic_vector_gradient_fourth_moment"),
                H("Two-coordinate physical gradient estimate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Take two real velocity components on a square with endpoints a and b, where a is at most b. The integration measure in each coordinate is Lebesgue measure restricted to the half-open interval from a to b. Supply their first and pure second coordinate derivatives by functions ux, uy, uxx and uyy, with the asserted derivative relations on every coordinate slice and continuous pure second derivatives on those slices. Assume the velocity and corresponding first derivatives agree at opposite faces, and that the sum of the squares of the two physical velocity components is at most M squared on the closed square, with M nonnegative.")),
                    Paragraph(Text("Assume integrability on the product measure of each first-derivative fourth power, each pure second-derivative square, and the square of the sum of the four first-derivative squares. Then the product integral of that last gradient quantity is at most thirty-six times M squared times the product integral of the sum of the four pure second-derivative squares. The argument applies the scalar periodic estimate on every coordinate slice, uses Fubini to place both directional estimates on the same square measure, and combines the four components by a finite-dimensional square bound. This statement does not yet identify the pure second-derivative energy with a Fourier Laplacian energy or prove an H2 tensor-product estimate."))),
                DescribeRole.Theorem))));
}
