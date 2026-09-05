using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Phase;

internal sealed class HeckeOstrowskiCoboundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The centered indicator of a fractional-part interval is an explicit finite "
            + "coboundary for rotation by alpha.",
        H("Hecke-Ostrowski Coboundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("hecke-ostrowski-coboundary"),
            DeclarationHandle.Create(
                "D5/S1/Phase/HeckeOstrowskiCoboundary.hecke_ostrowski_coboundary"),
            H("The interval discrepancy is an explicit coboundary"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For real alpha and x and natural q, the transfer function is the sum "
                        + "of fract(x - (j + 1) alpha) over j below q. The formula identifies "
                        + "the centered indicator of the interval from zero to fract(q alpha) "
                        + "with the transfer difference between x and x + alpha.")),
                Paragraph(Text(
                    "The escape lemma proves the exact two-branch formula for fract(x - t) "
                        + "from Int.fract_eq_iff. The finite transfer difference then "
                        + "telescopes to fract(x - q alpha) - fract(x).")),
                Paragraph(Text(
                    "No irrationality assumption on alpha is needed; the endpoint and q = 0 "
                        + "cases are included in the same identity."))),
            DescribeRole.Theorem))));

    private static Formula Fract(Formula value) =>
        Seq(Operatorname, Grp(F.Id("fract")), Open, value, Close);

    private static Formula Transfer(Formula alpha, Formula q, Formula x) =>
        Seq(Operatorname, Grp(F.Id("transferFunction")), Open,
            alpha, Comma, Sp, q, Comma, Sp, x, Close);

    private static Formula TheoremFormula()
    {
        Formula q = F.Id("q");
        Formula x = F.Id("x");
        Formula qa = Seq(q, Alpha);
        Formula condition = Seq(Fract(x), Sp, Lt, Sp, Fract(qa));
        Formula indicator = Seq(
            Operatorname, Grp(F.Id("if")), Open, condition, Comma, Sp,
            D(1), Comma, Sp, D(0), Close);

        return Disp(Seq(
            Forall, Sp, Alpha, Comma, Sp, x, Sp, InMacro, Sp,
            Mathbb, Grp(F.Id("R")), Comma, Sp,
            q, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Esc,
            indicator, Sp, Minus, Sp, Fract(qa), Sp, Eq, Sp,
            Transfer(Alpha, q, x), Sp, Minus, Sp,
            Transfer(Alpha, q, Seq(x, Plus, Alpha)), Dot));
    }
}
