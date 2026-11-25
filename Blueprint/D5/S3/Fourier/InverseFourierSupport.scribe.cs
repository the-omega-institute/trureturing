using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class InverseFourierSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire function with a square-integrable real restriction has inverse Fourier support bounded by its directional exponential type.",
        H("Inverse Fourier support at the directional half-width"),
        Blocks(Describe.Lean(
            DescribeId.Create("inverse-fourier-l2-support-at-directional-half-width"),
            DeclarationHandle.Create("D5/S3/Fourier/InverseFourierSupport.inverse_fourier_L2_support"),
            H("Almost-everywhere support of the inverse Fourier class"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be entire with square-integrable real restriction. Suppose its norm "
                    + "is bounded by C times (1 + |z|) to the power m times exp(a |Im z|). "
                    + "The L2 inverse of the function xi mapped to F(2 pi xi) vanishes almost "
                    + "everywhere where |t| exceeds a.")),
                Paragraph(Text(
                    "Multiplying F by sinc(epsilon z) to the power m + 2 gives inverse-square "
                    + "decay in each horizontal strip. Cauchy integration on rectangles shifts "
                    + "the angular inverse integral with phase exp(i t z) into the upper half "
                    + "plane for the positive tail. Reflection gives the negative tail. Each "
                    + "regularized inverse is supported at half-width a + (m + 2) epsilon. "
                    + "Classical inversion and forward L1/L2 agreement identify this inverse "
                    + "with the L2 inverse. The regularized restrictions converge in L2 by "
                    + "dominated convergence, and an almost-everywhere convergent subsequence "
                    + "of the inverses gives the limiting half-width a."))),
            DescribeRole.Theorem))));
}
