using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier;

internal sealed class GoldenReciprocityFixedPointDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden reciprocity and unit periodicity determine the value at the golden fixed point.",
        H("Golden Reciprocity at Its Fixed Point"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-reciprocity-fixed-point"),
                DeclarationHandle.Create(
                    "D5/S3/Fourier/GoldenReciprocityFixedPoint."
                    + "golden_reciprocity_fixed_point"),
                H("The reciprocal golden argument closes the functional equation"),
                StatementSource.FromAuthor(FixedPointFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c be periodic with period one and suppose that at every irrational "
                        + "argument y the reciprocal relation is g(y) = y c(y) + c(1/y). "
                        + "Set x = 1/phi. Since 1/x = phi = x + 1, periodicity identifies "
                        + "c(1/x) with c(x).")),
                    Paragraph(Text(
                        "Substitution gives g(x) = (x + 1)c(x). The pinned Mathlib golden-ratio "
                        + "identities identify x + 1 with phi, and division by the nonzero "
                        + "golden ratio yields c(x) = g(x)/phi.")),
                    Paragraph(Text(
                        "This closes only the leading exact fixed-point equation and its value "
                        + "consequence in theorem-form 6.190, clause 2. It does not claim the "
                        + "later numerical extrapolation, decimal values, method assessment, "
                        + "or the registration statements in that atom."))),
                DescribeRole.Theorem))));

    private static Formula FixedPointFormula()
    {
        Formula c = F.Id("c");
        Formula g = F.Id("g");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula cx = Seq(c, Open, x, Close);
        Formula gx = Seq(g, Open, x, Close);

        return Disp(Seq(
            x, Sp, Eq, Sp, Frac, Grp(D(1)), Grp(Varphi), Comma, Quad, Sp,
            F.Id("Periodic"), Open, c, Comma, Sp, D(1), Close, Comma, RowBreak,
            Forall, Sp, y, Comma, Sp,
            F.Id("Irrational"), Open, y, Close, Sp, Rightarrow, Sp,
            g, Open, y, Close, Sp, Eq, Sp,
            y, Sp, Cdot, Sp, c, Open, y, Close, Sp, Plus, Sp,
            c, Open, Frac, Grp(D(1)), Grp(y), Close, Comma, RowBreak,
            Rightarrow, Sp,
            cx, Sp, Cdot, Sp, Open, x, Sp, Plus, Sp, D(1), Close,
            Sp, Eq, Sp, gx, Sp, Land, Sp,
            cx, Sp, Eq, Sp, Frac, Grp(gx), Grp(Varphi), Dot));
    }
}
