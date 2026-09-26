using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class FixedSupportFisherGapDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/FixedSupportFisherGap.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized probability curve on one fixed finite support has a strict Fisher-information gap.",
        H("Fixed-support Fisher gap"),
        Blocks(
            Paragraph(Text(
                "Let ι be any finite index type. The same support values x(j) and the same "
                + "nonnegative weight curve p(j,u) are used for every parameter u in the open "
                + "interval (2a−1,1). The curve is normalized, has mean a, and has second "
                + "moment (1+u)/2 throughout that interval. The Fisher sum is filtered to the "
                + "indices with positive current weight; indices of weight zero contribute zero "
                + "because nonnegative differentiable weights have zero derivative at a local "
                + "minimum.")),
            Describe.Lean(
                DescribeId.Create("fixed-support-fisher-gap-result"),
                DeclarationHandle.Create(Module + "result"),
                H("The exact gap"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Assume 0<a<1, every support point lies in [−1,1], every weight is "
                        + "differentiable on (2a−1,1), and the displayed normalization and two "
                        + "moment identities hold for the same curve at every parameter. If its "
                        + "actual positive-support Fisher sum is at most R(1−a²)/((1−u)(1+u−2a²)) "
                        + "pointwise, then R is at least 1+a² divided by "
                        + "(1+4a+2(1+a) log 2)². The conclusion is uniform over the arbitrary "
                        + "finite fixed support and does not assume endpoint continuity or a "
                        + "limiting value of p.")),
                    Paragraph(Text(
                        "The proof differentiates the three same-curve constraints, applies the "
                        + "finite weighted Cauchy–Schwarz inequality with zero-weight terms removed, "
                        + "and controls the resulting normalized mean along the interval. Monotonicity "
                        + "and continuity of the auxiliary expressions at the left endpoint produce "
                        + "the exact log 2 constant.")),
                    Paragraph(Text(
                        "For nonvacuity, the support [−1,1/2,1] with a=1/2 and R=4/3 and weights "
                        + "((1+2u)/12, 2(1−u)/3, (1+2u)/4) satisfies all hypotheses on (0,1); "
                        + "all three weights are strictly positive there, so the filtered Fisher "
                        + "sum is the full three-term sum.")))))));

    private static Formula ResultFormula()
    {
        var a = F.Id("a");
        var r = F.Id("R");
        var u = F.Id("u");
        var j = F.Id("j");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var interval = Seq(Open, D(2), a, Minus, D(1), Comma, D(1), Close);
        var xj = Seq(F.Id("x"), Underscore, Grp(j));
        var pj = Seq(F.Id("p"), Underscore, Grp(j));
        var weight = Seq(pj, Open, u, Close);
        var sum = Seq(Sum, Underscore, Grp(j, InMacro, Sp, Iota));
        var squareA = Seq(a, Caret, Grp(D(2)));
        var constant = Seq(D(1), Plus, D(4), a, Plus, D(2), Open, D(1), Plus, a,
            Close, Log, Sp, D(2));
        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Iota, Sp, F.Text, Grp(F.Id("finite")), Comma, Sp,
                Forall, Sp, a, Comma, r, InMacro, Sp, real, Comma, Sp,
                Forall, Sp, F.Id("x"), Colon, Iota, To, real, Comma, Sp,
                Forall, Sp, F.Id("p"), Colon, Iota, To, real, To, real, Comma),
            Seq(F.Id("J"), Eq, interval, Comma, Sp,
                D(0), Lt, a, Lt, D(1), Comma),
            Seq(Forall, Sp, j, InMacro, Sp, Iota, Comma, Sp,
                xj, InMacro, Sp, OpenBracket, Minus, D(1), Comma, D(1), CloseBracket,
                Comma, Sp, pj, Sp, F.Text,
                Grp(F.Id("differentiable"), Sp, F.Id("on")), Sp, F.Id("J"), Comma),
            Seq(Forall, Sp, u, InMacro, Sp, F.Id("J"), Comma, Sp,
                Forall, Sp, j, InMacro, Sp, Iota, Comma, Sp, D(0), Le, Sp, weight, Comma),
            Seq(Forall, Sp, u, InMacro, Sp, F.Id("J"), Comma, Sp,
                sum, weight, Eq, D(1), Comma, Sp,
                sum, weight, xj, Eq, a, Comma, Sp,
                sum, weight, xj, Caret, Grp(D(2)), Eq,
                Quotient(Seq(D(1), Plus, u), D(2)), Comma),
            Seq(Forall, Sp, u, InMacro, Sp, F.Id("J"), Comma, Sp,
                Sum, Underscore, Grp(j, InMacro, Sp, Iota, Colon, D(0), Lt, weight),
                Quotient(Seq(Open, pj, Apos, Open, u, Close, Close, Caret, Grp(D(2))), weight),
                Le, Sp, Quotient(Seq(r, Open, D(1), Minus, squareA, Close),
                    Seq(Open, D(1), Minus, u, Close, Open, D(1), Plus, u,
                        Minus, D(2), squareA, Close))),
            Seq(Longrightarrow, Sp, D(1), Plus,
                Quotient(squareA, Seq(Open, constant, Close, Caret, Grp(D(2)))),
                Le, Sp, r)
        ]));
    }

    private static Formula Quotient(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));
}
