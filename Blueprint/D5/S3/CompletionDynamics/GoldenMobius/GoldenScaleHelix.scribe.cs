using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.CompletionDynamics.GoldenMobius;

internal sealed class GoldenScaleHelixDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/CompletionDynamics/GoldenMobius/GoldenScaleHelix.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden completion lifts to a scale helix with period two log phi and orientation reversal.",
        H("Golden Scale Helix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-period-is-contraction-length"),
                DeclarationHandle.Create(
                    Prefix + "golden_scale_period_eq_neg_log_multiplier"),
                H("The golden period is the logarithmic contraction length"),
                StatementSource.FromAuthor(PeriodFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The positive logarithmic scale period is defined as twice the logarithm "
                            + "of the golden ratio.")),
                    Paragraph(Text(
                        "It equals the negative logarithm of the absolute canonical projective "
                            + "multiplier, linking one local contraction step to one global scale "
                            + "turn.")),
                    Paragraph(Text(
                        "The universal-cover helix raises completion level, translates by one "
                            + "period, and reverses an orientation sheet; two steps restore "
                            + "orientation."))),
                DescribeRole.Theorem))));

    private static Formula PeriodFormula() => Disp(Seq(
        Sub(F.Id("L"), F.Id("phi")), Sp, Eq, Sp,
        Minus, Call("log", Call("abs", Sub(F.Id("lambda"), F.Id("phi"))))));
}
