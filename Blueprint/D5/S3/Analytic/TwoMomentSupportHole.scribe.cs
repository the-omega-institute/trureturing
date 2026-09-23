using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class TwoMomentSupportHoleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/TwoMomentSupportHole.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Moving probability atoms determine the exact price of excluding a support interval from a noisy two-moment model.",
        H("Two-Moment Support Hole"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-moment-support-hole-feasible-masses"),
                DeclarationHandle.Create(Prefix + "twoMomentMassSet"),
                H("Actual finite probability pairs"),
                StatementSource.FromAuthor(MassSetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The designated atom is at one. Residual nodes lie in [a,1), outside the specified hole, and comparison nodes lie in [a,b]. Both measures have nonnegative weights and total mass one. The first two actual Prony moments differ by at most epsilon. Arbitrary finite cardinalities are allowed, and the exclusion of one from residual nodes makes w the actual endpoint mass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("two-moment-support-hole-sharp-loss"),
                DeclarationHandle.Create(Prefix + "two_moment_support_hole_sharp"),
                H("Attained maxima and exact support-loss law"),
                StatementSource.FromAuthor(SharpFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the stated continuous geometric parameters, epsilon=(1-b)(b-t)/(2+t) yields a moving residual atom at t in the unrestricted optimizer. Excluding (l,r) replaces it by explicit nonnegative masses at l and r. Both optimizers are normalized and saturate the actual first two moment errors. Quadratic certificates bound all competing finite laws and yield two IsGreatest conclusions. Their exact difference is (1-wc)(t-l)(r-t)/((1-l)(1-r)), including boundary zero loss. The complete all-noise curve, fixed-grid consequence and optimal transformed grid have ordinary proofs in the theory; this declaration formalizes the general moving-support and hole comparison."))),
                DescribeRole.Theorem))));

    private static Formula I(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Sum(Formula index, Formula value) =>
        Seq(FormulaDsl.Sum, Underscore, Grp(index), Sp, value);

    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Interval(Formula left, Formula right) =>
        Seq(OpenBracket, left, Comma, Sp, right, CloseBracket);

    private static Formula MassSetFormula()
    {
        var a = F.Id("a"); var b = F.Id("b"); var e = Varepsilon;
        var h = F.Id("H"); var w = F.Id("w");
        var n = F.Id("n"); var m = F.Id("m");
        var z = F.Id("z"); var u = F.Id("u");
        var y = F.Id("y"); var v = F.Id("v");
        var i = F.Id("i"); var j = F.Id("j");
        var firstError = Seq(w, Plus, Call("Prony", z, u, D(1)), Minus,
            Call("Prony", y, v, D(1)));
        var secondError = Seq(w, Plus, Call("Prony", z, u, D(2)), Minus,
            Call("Prony", y, v, D(2)));
        return Disp(Seq(
            I(F.Id("M"), h), Open, a, Comma, b, Comma, e, Close, Sp, Eq, Sp,
            OpenBrace, w, Sp, Mid, Sp, D(0), Sp, Le, Sp, w, Sp, Land, Sp,
            Exists, Sp, n, Comma, m, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")),
                Comma, Sp,
            z, Comma, u, Colon, Sp, Call("Fin", n), Sp, To, Sp,
                Mathbb, Grp(F.Id("R")), Comma, Sp,
            y, Comma, v, Colon, Sp, Call("Fin", m), Sp, To, Sp,
                Mathbb, Grp(F.Id("R")), Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp,
                a, Sp, Le, Sp, Call("z", i), Sp, Land, Sp,
                Call("z", i), Sp, Lt, Sp, D(1), Sp, Land, Sp,
                Neg, Open, Call("z", i), Sp, InMacro, Sp, h, Close, Close,
                Sp, Land, Sp,
            Open, Forall, Sp, j, Comma, Sp,
                Call("y", j), Sp, InMacro, Sp, Interval(a, b), Close, Sp, Land, Sp,
            Open, Forall, Sp, i, Comma, Sp, D(0), Sp, Le, Sp, Call("u", i), Close,
                Sp, Land, Sp,
            Open, Forall, Sp, j, Comma, Sp, D(0), Sp, Le, Sp, Call("v", j), Close,
                Sp, Land, Sp,
            w, Plus, Sum(i, Call("u", i)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Sum(j, Call("v", j)), Sp, Eq, Sp, D(1), Sp, Land, Sp,
            Abs(firstError), Sp, Le, Sp, e, Sp, Land, Sp,
            Abs(secondError), Sp, Le, Sp, e, Sp, CloseBrace));
    }

    private static Formula SharpFormula()
    {
        var a = F.Id("a"); var b = F.Id("b");
        var l = F.Id("l"); var r = F.Id("r"); var t = F.Id("t");
        var e = Varepsilon; var c = F.Id("c");
        var wc = I(F.Id("w"), F.Id("c"));
        var wh = I(F.Id("w"), F.Id("h"));
        var oneMinusB = Seq(D(1), Minus, b);
        var twoPlusT = Seq(D(2), Plus, t);
        return Disp(Seq(
            Forall, Sp, a, Comma, b, Comma, l, Comma, r, Comma, t,
                Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
            Open, D(0), Sp, Le, Sp, a, Sp, Land, Sp,
                a, Sp, Lt, Sp, b, Sp, Land, Sp,
                b, Sp, Lt, Sp, D(1), Sp, Land, Sp,
                a, Sp, Le, Sp, l, Sp, Land, Sp,
                l, Sp, Lt, Sp, r, Sp, Land, Sp,
                r, Sp, Le, Sp, b, Sp, Land, Sp,
                l, Sp, Le, Sp, t, Sp, Land, Sp,
                t, Sp, Le, Sp, r, Sp, Land, Sp,
                D(2), t, Sp, Le, Sp, a, Plus, b, Sp, Land, Sp,
                l, Plus, r, Sp, Le, Sp, a, Plus, b, Close,
            Sp, Longrightarrow, Sp,
            F.Text, Grp(F.Id("let"), Sp), Sp,
            e, Sp, Colon, Eq, Sp, Frac,
                Grp(Open, oneMinusB, Close, Open, b, Minus, t, Close),
                Grp(twoPlusT), Semi, Sp,
            c, Sp, Colon, Eq, Sp, Frac,
                Grp(Open, oneMinusB, Close, Open, D(2), Plus, b, Close),
                Grp(twoPlusT), Semi, Sp,
            wc, Sp, Colon, Eq, Sp, D(1), Minus,
                Frac, Grp(c), Grp(D(1), Minus, t), Semi, Sp,
            wh, Sp, Colon, Eq, Sp,
                Frac,
                    Grp(Open, b, Minus, l, Close, Open, b, Minus, r, Close,
                        Plus, e, Open, D(1), Plus, l, Plus, r, Close),
                    Grp(Open, D(1), Minus, l, Close, Open, D(1), Minus, r, Close),
                Semi, Sp,
            Call("IsGreatest",
                Seq(I(F.Id("M"), Emptyset), Open, a, Comma, b, Comma, e, Close), wc),
                Sp, Land, Sp,
            Call("IsGreatest",
                Seq(I(F.Id("M"), Seq(Open, l, Comma, r, Close)),
                    Open, a, Comma, b, Comma, e, Close), wh), Sp, Land, Sp,
            wc, Minus, wh, Sp, Eq, Sp,
                Frac,
                    Grp(Open, D(1), Minus, wc, Close,
                        Open, t, Minus, l, Close, Open, r, Minus, t, Close),
                    Grp(Open, D(1), Minus, l, Close, Open, D(1), Minus, r, Close)));
    }
}
