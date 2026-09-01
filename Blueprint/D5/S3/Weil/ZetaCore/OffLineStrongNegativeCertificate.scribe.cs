using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaCore;

internal sealed class OffLineStrongNegativeCertificateDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every off-line zero yields an admissible shift with a quantitative strong negative certificate.",
        H("Off-Line Strong Negative Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("off-line-strong-negative-certificate"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/ZetaCore/OffLineStrongNegativeCertificate.off_line_strong_negative_certificate"),
                H("Off-line strong negative certificate"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("rho"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Sp,
                    Forall, Sp, F.Id("delta"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Forall, Sp, F.Id("gamma"), InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
                    Open, F.Id("rho"), Eq, Frac, Grp(D(1)), Grp(D(2)), Plus, F.Id("delta"),
                    Plus, F.Id("i"), Cdot, Sp, F.Id("gamma"), Land, Sp,
                    D(0), Lt, F.Id("delta"), Land, Sp,
                    F.Id("xiReading"), Open, F.Id("rho"), Close, Eq, D(0), Close, Sp,
                    Rightarrow, Sp, Exists, Sp, F.Id("omega"), InMacro, Mathbb, Grp(F.Id("R")),
                    Comma, Sp, D(0), Lt, F.Id("omega"), Land, Sp,
                    F.Id("omega"), Lt, F.Id("delta"), Land, Sp,
                    F.Id("xiReading"), Open, F.Id("rho"), Minus, D(2), Cdot, Sp,
                    F.Id("omega"), Close, Neq, D(0), Land, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close,
                    Eq, Minus, Frac, Grp(D(1)), Grp(F.Id("omega"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close), Land, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close, Lt, D(0), Land, Sp,
                    F.Id("diagonalValue"), Open, F.Id("omega"), Comma,
                    Minus, F.Id("gamma"), Plus, F.Id("i"), Cdot, Sp,
                    Open, F.Id("delta"), Minus, F.Id("omega"), Close, Close,
                    Leq, Minus, Frac, Grp(D(4)), Grp(F.Id("delta"), Caret, D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The entire shifted xi reading cannot vanish throughout an interval: "
                            + "analytic isolation and the value xiReading zero equals one half "
                            + "produce a positive shift below the off-line displacement where "
                            + "the shifted reading is nonzero.")),
                    Paragraph(Text(
                        "At that shift, the frozen one-point computation gives the exact "
                            + "negative reciprocal value, strict negativity, and the sharp "
                            + "minus-four-over-delta-squared bound."))),
                DescribeRole.Theorem)),
        []));
}
