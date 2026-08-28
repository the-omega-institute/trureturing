using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Limits;

internal sealed class EulerCountertermUniquenessDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Constants/Limits/EulerCountertermUniqueness.euler_counterterm_unique";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Euler-Mascheroni constant is the unique finite counterterm for the "
            + "harmonic-logarithmic residual.",
        H("Euler Counterterm Uniqueness"),
        Blocks(Describe.Lean(
            DescribeId.Create("euler-counterterm-uniqueness"),
            DeclarationHandle.Create(Declaration),
            H("A vanishing residual uniquely determines the counterterm"),
            StatementSource.FromAuthor(Disp(Seq(
                Forall, Sp, F.Id("c"), InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                Open, Lim, Underscore, Grp(F.Id("n"), To, Infty), Sp,
                Open, F.Id("H"), Underscore, F.Id("n"), Sp, Minus, Sp,
                Log, Sp, F.Id("n"), Sp, Minus, Sp, F.Id("c"), Close,
                Sp, Eq, Sp, D(0), Close, Sp, Rightarrow, Sp,
                F.Id("c"), Sp, Eq, Sp, GammaLower, Dot))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The premise says that subtracting c from H_n - log n leaves a sequence "
                        + "tending to zero. Adding c back gives a second limit of the canonical "
                        + "harmonic-logarithmic sequence.")),
                Paragraph(Text(
                    "Mathlib proves that the same sequence tends to the Euler-Mascheroni "
                        + "constant. Uniqueness of limits in the real topology identifies the "
                        + "two constants."))),
            DescribeRole.Theorem))));
}
