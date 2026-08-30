using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class EulerCountertermExistenceAndPiDualityDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Limits/EulerCountertermExistenceAndPiDuality."
            + "euler_counterterm_existence_and_pi_duality";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Euler's constant supplies the finite harmonic-log counterterm, while pi eliminates "
            + "the standard Gaussian Fourier self-duality defect.",
        H("Euler Counterterm Existence and the Pi Contrast"),
        Blocks(Describe.Lean(
            DescribeId.Create("euler-counterterm-existence-and-pi-contrast"),
            DeclarationHandle.Create(Declaration),
            H("Gamma supplies the counterterm and pi removes the duality defect"),
            StatementSource.FromAuthor(ContractFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Pinned Mathlib proves that H_n minus log n tends to the Euler-Mascheroni "
                        + "constant. Subtracting that concrete constant therefore leaves a "
                        + "sequence tending to zero.")),
                Paragraph(Text(
                    "For the second conjunct, g_pi is the real Gaussian exp(-pi x^2), and its "
                        + "defect is its standard real Fourier transform minus itself. The "
                        + "repository's Gaussian self-duality theorem makes that defect zero."))),
            DescribeRole.Theorem))));

    private static Formula ContractFormula()
    {
        Formula n = F.Id("n");
        Formula gaussianPi = Seq(F.Id("g"), Underscore, Pi);

        return Disp(Seq(
            OpenBracket, ResidualLimit(GammaLower, n), CloseBracket,
            Sp, Land, RowBreak, Grp(),
            OpenBracket, Widehat, Grp(gaussianPi), Sp, Minus, Sp,
            gaussianPi, Sp, Eq, Sp, D(0), CloseBracket, Dot));
    }

    private static Formula ResidualLimit(Formula counterterm, Formula n) => Seq(
        Lim, Underscore, Grp(n, To, Infty), Sp,
        Open, F.Id("H"), Underscore, n, Sp, Minus, Sp,
        Log, Sp, n, Sp, Minus, Sp, counterterm, Close,
        Sp, Eq, Sp, D(0));
}
