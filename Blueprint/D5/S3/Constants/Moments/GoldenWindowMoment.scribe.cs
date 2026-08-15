using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class GoldenWindowMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every natural power moment of the translated golden window has a closed Binet form.",
        H("Golden Window Moments"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-window-power-moment"),
                DeclarationHandle.Create(
                    "D5/S3/Constants/Moments/GoldenWindowMoment.golden_window_moment"),
                H("The golden window power moments have a Binet form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("j"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
                    Int, Underscore, Grp(Minus, Varphi), Caret,
                    Grp(Varphi, Caret, Grp(Minus, D(1))), Sp,
                    Open, D(1), Plus, F.Id("x"), Close, Caret, F.Id("j"), Sp, F.Id("dx"),
                    Sp, Eq, Sp,
                    Frac,
                    Grp(
                        Varphi, Caret, Grp(F.Id("j"), Plus, D(1)), Sp, Minus, Sp,
                        Grp(Minus, Varphi, Caret, Grp(Minus, D(1))), Caret,
                        Grp(F.Id("j"), Plus, D(1))),
                    Grp(F.Id("j"), Plus, D(1)), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Translation by one sends the endpoints -phi and phi^-1 to "
                            + "-phi^-1 and phi. The pinned Mathlib theorem integral_pow then "
                            + "evaluates the translated monomial exactly.")),
                    Paragraph(Text(
                        "The proof directly reuses intervalIntegral.integral_comp_add_right, "
                            + "integral_pow, Real.inv_goldenRatio, Real.one_sub_goldenConj, and "
                            + "Real.one_sub_goldenRatio. Repository search found no equal or "
                            + "stronger golden-window moment declaration.")),
                    Paragraph(Text(
                        "This theorem formalizes only the window-moment sentence in source "
                            + "remark 27.187. It makes no claim about the surrounding reduction "
                            + "tower, the constants J1 or J2, or their numerical certificates."))),
                DescribeRole.Theorem))));
}
