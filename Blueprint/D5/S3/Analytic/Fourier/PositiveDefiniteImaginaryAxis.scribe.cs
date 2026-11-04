using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Fourier;

internal sealed class PositiveDefiniteImaginaryAxisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Imaginary radius bounds from finite positive semidefinite kernels.",
        H("Analytic positive definite functions"), Blocks(
            Describe.Lean(DescribeId.Create("positive-definite-binomial-weight"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weight"),
                H("Binomial stencil weight"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural k and j, weight(k,j)=(-1)^j choose(k,j)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-definite-weighted-shift"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.weighted_shift"),
                H("Signed forward difference"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real function g, natural k and real x, the sum of weight(k,j)g(x+j) over 0<=j<=k equals (-1)^k times the k-fold unit forward difference of g at x."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-definite-double-weighted-shift"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.double_weighted_shift"),
                H("Two-stencil convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real function g and natural k, the double sum of weight(k,i)weight(k,j)g(i-j) over 0<=i,j<=k equals (-1)^k times the 2k-fold unit forward difference of g at -k."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-definite-binomial-moment"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.finite_difference_moment"),
                H("Exact binomial quadratic moments"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/furuichi2022bounds")),
                Blocks(Paragraph(Text("For natural k and m with m at most 2k, put u(j)=(-1)^j choose(k,j) for j from zero to k. The sum over i and j of u(i)u(j)(i-j)^m is zero below degree 2k and is (-1)^k (2k)! at degree 2k. Two successive forward differences give the identity, including the case k=0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("positive-definite-imaginary-radius"),
                DeclarationHandle.Create("D5/S3/Analytic/Fourier/PositiveDefiniteImaginaryAxis.le_re_of_positiveDefinite"),
                H("The imaginary radius lower bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Fourier/furuichi2022bounds")),
                Blocks(Paragraph(Text("Let f map the real line to the complex numbers, be real valued, and have a positive semidefinite matrix with entries f(x(j)-x(i)) for every finite real family x. Suppose F is complex differentiable on the open disk of radius R centered at zero and agrees with f at every real x with absolute value less than R. For every real y with 0 at most y and y less than R, the real part of F(iy) is at least the real part of f(0).")),
                    Paragraph(Text("Binomial vectors test positive semidefiniteness at arbitrarily small real step sizes. The exact quadratic moments cancel every Taylor term below degree 2k. An analytic Taylor remainder and continuity give nonnegativity of (-1)^k times the even Taylor coefficient. Restriction of the power series to the real line shows that all coefficients are real. Odd powers therefore have zero real part on the imaginary radius, and summation of the nonnegative even terms gives the bound. The real-valued hypothesis is essential to this argument; no boundary regularity is assumed."))),
                DescribeRole.Theorem))));
}
