using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Laplace;

internal sealed class GaussianBoundaryContourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Laplace/GaussianBoundaryContour.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian integration of a holomorphic function with quadratic strip growth.",
        H("Shifting the regular Gaussian integral"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-exponent-re"),
                DeclarationHandle.Create(Prefix + "gaussian_exponent_re"),
                H("Real part of the vertical Gaussian exponent"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For real M, c, y, and t, the real part of (c+it)y+(c+it)^2/(2M^2) "
                    + "is cy+(c^2-t^2)/(2M^2). This is the real projection of the "
                    + "expanded Bromwich exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-polynomial-integrable"),
                DeclarationHandle.Create(Prefix + "gaussian_polynomial_integrable"),
                H("Integrable quadratic Gaussian majorant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive b, the function (1+|t|)^2 exp(-b t^2) is "
                    + "integrable on the real line. Gaussian moments of orders zero "
                    + "and two dominate the quadratic factor."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("regular-vertical-integrable"),
                DeclarationHandle.Create(Prefix + "regular_vertical_integrable"),
                H("Absolute convergence on vertical lines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let J be holomorphic on the open strip from minus one fifth to one "
                    + "and bounded by C times the square of one plus the absolute imaginary "
                    + "part on the closed strip from minus one sixth to three quarters. "
                    + "For every positive M, real y, and real c in that closed strip, the "
                    + "function J(c+it) exp((c+it)y+(c+it)^2/(2M^2)) is absolutely integrable "
                    + "in t. Its norm is bounded by a constant times a quadratic polynomial "
                    + "times exp(-t^2/(2M^2))."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-regular-bound"),
                DeclarationHandle.Create(Prefix + "gaussian_regular_bound"),
                H("A cubic bound after moving the contour"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the same strip assumptions there is a positive constant C "
                    + "such that, for every M at least one and every real y, the normalized "
                    + "Gaussian integral of J on real part three quarters has norm at most "
                    + "C M^3 exp(-y/6). Gaussian decay makes the horizontal cross-sections "
                    + "vanish at both ends of the strip, so the vertical integral equals "
                    + "the integral on real part minus one sixth. Rescaling t by M bounds "
                    + "the remaining quadratic Gaussian moment by a fixed constant times M^3."))),
                DescribeRole.Theorem))));
}
