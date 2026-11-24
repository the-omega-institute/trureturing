using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CharacterSums;

internal sealed class DirichletTriangleExplicitGammaDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/CharacterSums/DirichletTriangleExplicitGamma.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity corrections for triangular character sums",
        H("Parity corrections and centered Gamma transforms"),
        Blocks(
            Describe.Lean(DescribeId.Create("even-coefficients"),
                DeclarationHandle.Create(
                    Prefix + "evenCoeff"),
                H("Even trivial-zero coefficients"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For each natural n the index k=n+1 contributes the positive coefficient "
                    + "1/(2k(2k-1))."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-trivial-tail"),
                DeclarationHandle.Create(
                    Prefix + "evenT"),
                H("The even trivial-zero tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "At logarithmic argument y the complete tail is the sum of 1/(2k(2k-1)) "
                    + "times exp(-2ky), over all positive integers k."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("even-tail-nonnegative"),
                DeclarationHandle.Create(
                    Prefix + "evenT_nonneg"),
                H("Positivity of the even tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "Every term is nonnegative, so the totalized series is nonnegative at every "
                    + "real argument."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-tail-mass"),
                DeclarationHandle.Create(
                    Prefix + "evenT_le_mass"),
                H("The exact mass controls the even tail"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For y at least zero the even tail is summable and bounded by log(2). "
                    + "Its value at zero and its coefficient sum are exactly log(2), obtained "
                    + "from the digamma series at negative "
                    + "one half and the Gamma recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("character-parity"),
                DeclarationHandle.Create(
                    Prefix + "parity"),
                H("The parity index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "The complex parity index is zero for an even character and one for an odd "
                    + "character."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parity-correction"),
                DeclarationHandle.Create(
                    Prefix + "parityCorrection"),
                H("Endpoint and trivial-zero corrections"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For even characters the correction is 1-log(x)+(log(2)-1)/x minus the even "
                    + "tail at log(x). For odd characters it is -1+(log(x)+2-log(2))/x minus the "
                    + "existing trivial tail at log(x) divided by x."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("correction-initial-endpoint"),
                DeclarationHandle.Create(
                    Prefix + "parityCorrection_one"),
                H("The initial endpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every character the correction at x=1 is zero. The even and odd "
                    + "coefficient masses are respectively log(2) and 1-log(2)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correction-continuity"),
                DeclarationHandle.Create(
                    Prefix + "parityCorrection_continuousOn"),
                H("Continuity on the logarithmic half-axis"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "The correction evaluated at exp(y) is continuous for all y at least zero. "
                    + "Uniform absolute convergence of the complete tails includes the initial "
                    + "endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-integrable"),
                DeclarationHandle.Create(
                    Prefix + "exp_integrable"),
                H("Exponential damping"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex s with positive real part, exp(-sy) is integrable on the "
                    + "positive real half-axis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exponential-integral"),
                DeclarationHandle.Create(
                    Prefix + "exp_integral"),
                H("The exponential Laplace integral"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "For every complex s with positive real part, the integral of exp(-sy) on "
                    + "the positive real half-axis equals 1/s."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correction-laplace-integrable"),
                DeclarationHandle.Create(
                    Prefix + "parityCorrection_laplace_integrable"),
                H("Absolute convergence of the correction transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "The complete parity correction has an absolutely convergent Laplace "
                    + "transform at every positive damping abscissa. The linear endpoint term is "
                    + "controlled by the damped first moment, and the tails by their coefficient "
                    + "masses."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("correction-laplace-transform"),
                DeclarationHandle.Create(
                    Prefix + "parityCorrection_laplace"),
                H("The centered digamma transform"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                      "On the vertical line s=2+2 pi i t, for nonzero real t, the transform "
                    + "equals the difference digamma((s+a)/2)-digamma((2+a)/2), divided by "
                    + "2s(s+1), where a is the parity index. The nonzero frequency assumption "
                    + "keeps both digamma arguments in the integer complement required by the "
                    + "series interface. No pole or endpoint finite part remains in the resulting "
                    + "expression."))),
                DescribeRole.Theorem))));
}
