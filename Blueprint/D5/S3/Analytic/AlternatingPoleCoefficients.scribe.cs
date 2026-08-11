using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class AlternatingPoleCoefficientsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Analytic/AlternatingPoleCoefficients",
            "A pole of order d+1 at minus one has alternating binomial coefficients of degree d."),
        H("Alternating Coefficients from a Pole at Minus One"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("pole-order-controls-the-alternating-coefficient-polynomial"),
                H("Pole order controls the alternating coefficient polynomial"),
                LeanTheorem(
                    "D5/S3/Analytic/AlternatingPoleCoefficients.alternating_pole_coefficients"),
                Disp(Seq(
                    Forall, Sp, F.Id("d"), Comma, F.Id("n"), InMacro, Mathbb,
                    Grp(F.Id("N")), Comma, Esc,
                    OpenBracket, F.Id("v"), Caret, Grp(F.Id("n")), CloseBracket,
                    Open, D(1), Plus, F.Id("v"), Close, Caret,
                    Grp(Minus, Open, F.Id("d"), Plus, D(1), Close), Sp, Eq, Sp,
                    Open, Minus, D(1), Close, Caret, Grp(F.Id("n")), Cdot,
                    Operatorname, Grp(F.Id("choose")), Open, F.Id("d"), Plus,
                    F.Id("n"), Comma, F.Id("d"), Close, Dot)),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "For every nonnegative degree d, the formal expansion with a pole "
                        + "of order d+1 at minus one has nth coefficient equal to minus one "
                        + "to the nth power times choose(d+n,d). The binomial factor is a "
                        + "polynomial in n of degree d, so each increase in pole order raises "
                        + "the polynomial degree of the alternating coefficient envelope by "
                        + "one. This is the exact universal mechanism asserted by the source "
                        + "atom; its later row calculations are applications and numerical "
                        + "checks of this coefficient law.")),
                    Paragraph(Text(
                        "Mathlib was searched before proving. The pinned library already "
                        + "provides the coefficients of the inverse power of one minus X as "
                        + "`PowerSeries.invOneSubPow_val_succ_eq_mk_add_choose`, together "
                        + "with `PowerSeries.coeff_rescale`. The Lean theorem is therefore a "
                        + "declared thin honest wrapper: it rescales X by minus one and reads "
                        + "the resulting coefficient. No matching D5 theorem was found, and "
                        + "the wrapper adds the exact pole-at-minus-one formulation needed by "
                        + "the source atom without claiming a new library proof.")))
            ))));
}
