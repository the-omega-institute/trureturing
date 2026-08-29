using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Residuals;

internal sealed class GoldenResidualPeriodicityDocument : IScribeDocumentDefinition
{
    private const string Gid =
        "D5/S3/Observer/Residuals/GoldenResidualPeriodicity."
        + "unforced_golden_completion_has_no_off_line_fixed_point";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The unforced golden residual map has only zero as a fixed or finite-period point.",
        H("Golden Residual Periodicity"),
        Blocks(Describe.Lean(
            DescribeId.Create("unforced-golden-completion-has-no-off-line-fixed-point"),
            DeclarationHandle.Create(Gid),
            H("Unforced golden completion has no off-line fixed point"),
            StatementSource.FromAuthor(StatementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The residual update is constructed directly as multiplication by the "
                        + "negative reciprocal of Mathlib's real golden ratio. Its fixed-point "
                        + "equation holds exactly at zero.")),
                Paragraph(Text(
                    "For every positive natural period k, the k-fold iterate has multiplier "
                        + "the k-th power of that scalar. Its absolute value is strictly below "
                        + "one, so the periodic-point equation again holds exactly at zero."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula StatementFormula()
    {
        Formula delta = Delta;
        Formula k = F.Id("k");
        Formula x = F.Id("x");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula nat = Seq(Mathbb, Grp(F.Id("N")));
        Formula inversePhi = Seq(Phi, Caret, Grp(Minus, D(1)));
        Formula residualAt(Formula point) => Seq(Minus, inversePhi, Sp, point);
        Formula residualMap = Grp(Seq(
            Lambda, Sp, x, Colon, Sp, real, Comma, Sp, residualAt(x)));
        Formula fixedClause = Seq(
            Forall, Sp, delta, Colon, Sp, real, Comma, Sp,
            Open, residualAt(delta), Sp, Eq, Sp, delta, Sp, Iff, Sp,
            delta, Sp, Eq, Sp, D(0), Close);
        Formula periodicClause = Seq(
            Forall, Sp, k, Colon, Sp, nat, Comma, Sp,
            k, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
            Forall, Sp, delta, Colon, Sp, real, Comma, Sp,
            Open, Call("iterate", residualMap, k, delta), Sp, Eq, Sp, delta,
            Sp, Iff, Sp, delta, Sp, Eq, Sp, D(0), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            fixedClause, Sp, Land, RowBreak, Grp(),
            periodicClause, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
