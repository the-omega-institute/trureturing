using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class EulerResidualCancellationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Limits/EulerResidualCancellation.harmonic_log_euler_residual_tendsto_zero";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler-Mascheroni constant cancels the harmonic-logarithmic residual.",
        H("Euler Residual Cancellation"),
        Blocks(Describe.Lean(
            DescribeId.Create("euler-residual-cancellation"),
            DeclarationHandle.Create(Declaration),
            H("The harmonic-logarithmic Euler residual vanishes"),
            StatementSource.FromAuthor(Disp(Seq(
                Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                Open, F.Id("H"), Underscore, F.Id("n"), Sp, Minus, Sp,
                Log, Sp, F.Id("n"), Sp, Minus, Sp, GammaLower, Close,
                Sp, Eq, Sp, D(0), Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Mathlib proves that the harmonic numbers minus log n converge to the "
                        + "Euler-Mascheroni constant.")),
                Paragraph(Text(
                    "Subtracting that constant from the convergent sequence subtracts it "
                        + "from the limit, leaving zero."))),
            DescribeRole.Theorem))));
}
