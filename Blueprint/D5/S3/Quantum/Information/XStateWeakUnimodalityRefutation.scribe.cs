using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class XStateWeakUnimodalityRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/XStateWeakUnimodalityRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/yurischev2017extremal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Yurischev (arXiv:1702.03728, Quantum Inf. Process. 16, 249) writes the conditional entropy of a two-qubit X state through the function f_1 of Eq. (A1) on [0, 1] and supposes that it is weakly unimodal for every choice of the parameters p_1, ..., p_5 with nonnegative Shannon arguments. It is not: for p = (-2466, -1107, 187, -163, 1138)/2500 one has f_1(0) > f_1(27/50) < f_1(177/200) > f_1(1).",
        H("The X-state conditional entropy f_1 need not be weakly unimodal"),
        Blocks(
            Node("h2", "Binary Shannon entropy", H2Formula(),
                "h_2(a, b) = -a log_2 a - b log_2 b, written with Real.negMulLog t = -t log t divided by log 2.",
                "h2", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("h4", "Quaternary Shannon entropy", H4Formula(),
                "h_4(a, b, c, d) = -a log_2 a - b log_2 b - c log_2 c - d log_2 d.",
                "h4", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("w", "The parameter w", WFormula(),
                "w = (|p_3 + p_4| + |p_3 - p_4|)/4.",
                "wParam", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("r1", "The quantity r_1", RFormula(F.Id("r1"), true),
                "r_1 = (p_1 + p_5 x)^2 + 4 w^2 (1 - x^2).",
                "r1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("r2", "The quantity r_2", RFormula(F.Id("r2"), false),
                "r_2 = (p_1 - p_5 x)^2 + 4 w^2 (1 - x^2).",
                "r2", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("f1", "The function f_1", F1Formula(),
                "Eq. (A1): f_1(x) = -h_2((1 + p_2 x)/2, (1 - p_2 x)/2) + h_4((1 + p_2 x + sqrt r_1)/4, (1 + p_2 x - sqrt r_1)/4, (1 - p_2 x + sqrt r_2)/4, (1 - p_2 x - sqrt r_2)/4) for x in [0, 1].",
                "f1", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("args", "Nonnegative Shannon arguments", ArgsFormula(),
                "All six arguments of the Shannon functions in Eq. (A1) are nonnegative at x.",
                "ArgsNonneg", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("weak", "Weak unimodality", WeakFormula(),
                "Appendix, definition of weak unimodality: f is weakly unimodal on [a, b] if for some x_m in [a, b] it is weakly increasing for x <= x_m and weakly decreasing for x >= x_m; the analogous definition for the minimum is weakly decreasing and then weakly increasing.",
                "WeaklyUnimodal", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The unimodality hypothesis for f_1", ClaimFormula(),
                "For all real p_1, ..., p_5 such that every Shannon argument of Eq. (A1) is nonnegative for every x in [0, 1], the function x -> f_1(x) is weakly unimodal on [0, 1], in the maximum form or in the minimum form.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "A non-unimodal conditional entropy", Disp(new Formula.Not(F.Id("claim"))),
                "Take p = (-2466, -1107, 187, -163, 1138)/2500, so w = 187/5000. On [0, 1] the quadratic bounds (1 + p_2 x)^2 - r_1 >= 0 and (1 - p_2 x)^2 - r_2 >= 0, each a nonnegative combination of (1 - x)^2, x^2 and x (1 - x), make every Shannon argument nonnegative. At x = 0, 27/50, 177/200 and 1 the square roots are bracketed by rationals, every argument t lies in a rational interval [l, u] inside (0, 1], and l (-log u) <= -t log t <= u (-log l). Each log l and log u is bounded within 10^-8 by Real.abs_log_sub_add_sum_range_le after scaling by a power of 2 and by Real.log_two_near_10. This gives f_1 log 2 within 4 * 10^-8 of 0.033497172, 0.033489113, 0.033498565 and 0.033485902 at the four points, so f_1(0) > f_1(27/50) < f_1(177/200) > f_1(1). If f_1 were weakly increasing up to x_m and weakly decreasing after it, either 27/50 <= x_m contradicts f_1(0) > f_1(27/50), or x_m < 27/50 contradicts f_1(27/50) < f_1(177/200). In the minimum form, either 177/200 <= x_m contradicts f_1(27/50) < f_1(177/200), or x_m < 177/200 contradicts f_1(177/200) > f_1(1).",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yurischev-2017-xstate-unimodality"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("xunimodal-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula EqTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula LeTo(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));
    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula All(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, Colon, Sp, domain, Comma, Sp, body);
    private static Formula AllIn(Formula variable, Formula set, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, set, Comma, Sp, body);
    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Frac(Formula top, Formula bottom) => new Formula.Fraction(top, bottom);
    private static Formula Pow(Formula b, Formula e) => new Formula.Power(b, e);
    private static Formula Root(Formula x) => Seq(Sqrt, Grp(x));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Abs(Formula x) => Seq(Bar, x, Bar);
    private static Formula P(byte n) => new Formula.Subscript(F.Id("p"), D(n));
    private static Formula Icc(Formula a, Formula b) => Seq(OpenBracket, a, Comma, Sp, b, CloseBracket);
    private static Formula Nml(Formula t) => Call(F.Id("negMulLog"), t);
    private static Formula Log2() => Seq(Log, Sp, D(2));

    private static Formula H2Formula()
    {
        Formula a = F.Id("a"), b = F.Id("b");
        return Disp(All(a, Real(), All(b, Real(),
            EqTo(Call(F.Id("h2"), a, b), Frac(Add(Nml(a), Nml(b)), Log2())))));
    }

    private static Formula H4Formula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), c = F.Id("c"), d = F.Id("d");
        Formula sum = Add(Add(Add(Nml(a), Nml(b)), Nml(c)), Nml(d));
        return Disp(All(a, Real(), All(b, Real(), All(c, Real(), All(d, Real(),
            EqTo(Call(F.Id("h4"), a, b, c, d), Frac(sum, Log2())))))));
    }

    private static Formula WFormula() =>
        Disp(All(P(3), Real(), All(P(4), Real(),
            EqTo(Call(F.Id("wParam"), P(3), P(4)),
                Frac(Add(Abs(Add(P(3), P(4))), Abs(Sub(P(3), P(4)))), D(4))))));

    private static Formula RFormula(Formula name, bool plus)
    {
        Formula x = F.Id("x");
        Formula lin = plus ? Add(P(1), Mul(P(5), x)) : Sub(P(1), Mul(P(5), x));
        Formula value = Add(Pow(Parenthesized(lin), D(2)),
            Mul(Mul(D(4), Pow(Call(F.Id("wParam"), P(3), P(4)), D(2))), Parenthesized(Sub(D(1), Pow(x, D(2))))));
        return Disp(All(x, Real(), EqTo(Call(name, x, P(1), P(3), P(4), P(5)), value)));
    }

    private static Formula F1Formula()
    {
        Formula x = F.Id("x"), px = Mul(P(2), x);
        Formula s1 = Root(Call(F.Id("r1"), x, P(1), P(3), P(4), P(5)));
        Formula s2 = Root(Call(F.Id("r2"), x, P(1), P(3), P(4), P(5)));
        Formula value = Add(Seq(Minus, Call(F.Id("h2"), Frac(Add(D(1), px), D(2)), Frac(Sub(D(1), px), D(2)))),
            Call(F.Id("h4"), Frac(Add(Add(D(1), px), s1), D(4)), Frac(Sub(Add(D(1), px), s1), D(4)),
                Frac(Add(Sub(D(1), px), s2), D(4)), Frac(Sub(Sub(D(1), px), s2), D(4))));
        return Disp(All(x, Real(), EqTo(Call(F.Id("f1"), x, P(1), P(2), P(3), P(4), P(5)), value)));
    }

    private static Formula ArgsFormula()
    {
        Formula x = F.Id("x"), px = Mul(P(2), x);
        Formula s1 = Root(Call(F.Id("r1"), x, P(1), P(3), P(4), P(5)));
        Formula s2 = Root(Call(F.Id("r2"), x, P(1), P(3), P(4), P(5)));
        Formula body = And(And(And(LeTo(D(0), Frac(Add(D(1), px), D(2))), LeTo(D(0), Frac(Sub(D(1), px), D(2)))),
            And(LeTo(D(0), Frac(Add(Add(D(1), px), s1), D(4))), LeTo(D(0), Frac(Sub(Add(D(1), px), s1), D(4))))),
            And(LeTo(D(0), Frac(Add(Sub(D(1), px), s2), D(4))), LeTo(D(0), Frac(Sub(Sub(D(1), px), s2), D(4)))));
        return Disp(Logic(Call(F.Id("ArgsNonneg"), x, P(1), P(2), P(3), P(4), P(5)),
            FormulaLogicOperator.Iff, body));
    }

    private static Formula WeakFormula()
    {
        Formula f = F.Id("f"), a = F.Id("a"), b = F.Id("b"), m = new Formula.Subscript(F.Id("x"), F.Id("m"));
        Formula up = And(Call(F.Id("MonotoneOn"), f, Icc(a, m)), Call(F.Id("AntitoneOn"), f, Icc(m, b)));
        Formula down = And(Call(F.Id("AntitoneOn"), f, Icc(a, m)), Call(F.Id("MonotoneOn"), f, Icc(m, b)));
        Formula body = Seq(Exists, Sp, m, Sp, InMacro, Sp, Icc(a, b), Comma, Sp,
            Logic(up, FormulaLogicOperator.Or, down));
        return Disp(Logic(Call(F.Id("WeaklyUnimodal"), f, a, b), FormulaLogicOperator.Iff, body));
    }

    private static Formula ClaimFormula()
    {
        Formula x = F.Id("x");
        Formula ps = Seq(P(1), Comma, Sp, P(2), Comma, Sp, P(3), Comma, Sp, P(4), Comma, Sp, P(5));
        Formula admissible = AllIn(x, Icc(D(0), D(1)), Call(F.Id("ArgsNonneg"), x, P(1), P(2), P(3), P(4), P(5)));
        Formula f = Parenthesized(Seq(x, Sp, Mapsto, Sp, Call(F.Id("f1"), x, P(1), P(2), P(3), P(4), P(5))));
        Formula body = Logic(admissible, FormulaLogicOperator.Implies, Call(F.Id("WeaklyUnimodal"), f, D(0), D(1)));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, All(ps, Real(), body)));
    }
}
