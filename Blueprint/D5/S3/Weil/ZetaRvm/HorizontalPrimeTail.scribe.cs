using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaRvm;

internal sealed class HorizontalPrimeTailDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/ZetaRvm/HorizontalPrimeTail.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolutely convergent prime Fourier series of the actual horizontal zeta tail.",
        H("Prime realization of Littlewood's right boundary"),
        Blocks(
            Paragraph(Text("The tail is the actual Lebesgue integral of "
                + "log(norm(zeta(sigma+it))) over sigma > R. The coefficient is "
                + "vonMangoldt(n)/(n^R log(n)^2), with total real division at n=0 and n=1. "
                + "Both terms are zero. The theorem includes R=2, t=0 and every negative "
                + "real height. The central RH sign E <= 0 remains unproved.")),
            Describe.Lean(DescribeId.Create("prime-tail-coefficient"),
                DeclarationHandle.Create(Prefix + "zetaHorizontalPrimeCoeff"),
                H("The prime-power coefficient"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real R and natural n, the coefficient "
                    + "is Lambda(n) divided by n^R times log(n)^2. The series keeps its "
                    + "original natural-number indexing, including zero and one."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-prime-tail-expansion"),
                DeclarationHandle.Create(Prefix + "zetaHorizontalLogTail_prime_expansion"),
                H("Absolute convergence and the exact prime Fourier expansion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every R >= 2 and every real t, the absolute "
                    + "coefficients are summable, the absolute cosine-weighted coefficients "
                    + "are summable, and the actual tail equals their cosine series. "
                    + "Mathlib's verified von Mangoldt L-series gives the logarithmic "
                    + "derivative. Positivity of Re zeta in this half-plane permits local "
                    + "differentiation of its genuine principal logarithm. The actual "
                    + "lognorm tends to zero at infinity, so the first integration "
                    + "identifies it with the series weighted by one logarithm. The "
                    + "second integration yields the squared-logarithm denominator. "
                    + "Each interchange of series and integral has its own summable "
                    + "integral-of-norm bound; no Euler logarithm formula is assumed.")),
                    Paragraph(Text("The cpow calculation adapts per_n_line_integral in "
                        + "ZetaExplicit/VerticalLine.lean, from anthropics/zeta-23-lean "
                        + "commit 3635e74826a4c1fcece7d1cd2b6fa75e43a00510, "
                        + "copyright Anthropic PBC, Apache-2.0. This is a formalized "
                        + "application of classical Dirichlet-series analysis."))),
                DescribeRole.Theorem))));
}
