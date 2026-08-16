using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Detection;

internal sealed class LogTimeDoublingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A log-time shift by log 2 / delta doubles a positive exponential mode.",
        H("Log-Time Doubling"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("log-time-shift-doubles-exponential-mode"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Detection/LogTimeDoubling."
                    + "log_time_shift_doubles_exponential_mode"),
                H("The logarithmic lifetime shift doubles the growing mode"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, DeltaLower, Comma, F.Id("u"), InMacro,
                    Mathbb, Grp(F.Id("R")), Comma, Esc,
                    DeltaLower, Gt, D(0), Sp, Rightarrow, Sp,
                    Exp, Open, DeltaLower, Open,
                    F.Id("u"), Plus,
                    Frac, Grp(Log, Sp, D(2)), Grp(DeltaLower),
                    Close, Close, Sp, Eq, Sp,
                    D(2), Sp, Exp, Open,
                    DeltaLower, Thin, F.Id("u"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let delta be a positive displacement from the critical line and u "
                        + "the logarithmic time coordinate. Advancing u by log 2 / delta "
                        + "multiplies the growing exponential mode by exactly two.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Real.exp_add and Real.exp_log. The Lean proof "
                        + "only cancels the nonzero delta and applies those two identities, so "
                        + "it is a thin wrapper around the library facts rather than a second "
                        + "proof of exponential or logarithmic laws.")),
                    Paragraph(Text(
                        "This theorem closes the exact logarithmic-time doubling formula. It "
                        + "does not formalize the surrounding particle analogy, spectral-line "
                        + "interpretation, numerical table, or claims about physical time."))),
                DescribeRole.Theorem)),
        []));
}
