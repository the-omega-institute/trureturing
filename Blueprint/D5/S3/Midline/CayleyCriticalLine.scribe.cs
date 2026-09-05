using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Midline;

internal sealed class CayleyCriticalLineDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar Cayley ratio has unit modulus exactly on the critical line.",
        H("Cayley Ratio and the Critical Line"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-ratio-critical-line"),
                DeclarationHandle.Create(
                    "D5/S3/Midline/CayleyCriticalLine."
                        + "cayley_ratio_norm_one_iff_critical_line"),
                H("Unit circle corresponds to the critical line"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("s"), InMacro,
                    Mathbb, Grp(F.Id("C")), Comma, Esc,
                    Lvert, Frac,
                        Grp(F.Id("s"), Sp, Minus, Sp, D(1)),
                        Grp(F.Id("s")), Rvert,
                    Sp, Eq, Sp, D(1),
                    Sp, Leftrightarrow, Sp,
                    Re, Open, F.Id("s"), Close,
                    Sp, Eq, Sp, Frac, Grp(D(1)), Grp(D(2)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The proof treats the totalized division value at zero separately. "
                            + "For a nonzero parameter, the squared norm defect is "
                            + "(1 - 2 Re(s)) divided by the norm square of s.")),
                    Paragraph(Text(
                        "Thus unit modulus is equivalent to vanishing horizontal "
                            + "displacement from real part one half."))),
                DescribeRole.Theorem))));
}
