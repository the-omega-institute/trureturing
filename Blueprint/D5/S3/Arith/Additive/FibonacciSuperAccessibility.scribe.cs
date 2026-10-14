using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class FibonacciSuperAccessibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/FibonacciSuperAccessibility.";
    private static readonly LibraryNoteRef Landman =
        LibraryNoteRef.Create("D5/L/Certificates/landman2023fibonaccisuperaccessibility");
    private static readonly LibraryNoteRef Wesley =
        LibraryNoteRef.Create("D5/L/Certificates/wesley2026fibonaccimodulus29");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rotation coloring gives a kernel-checked refutation of 2-super-accessibility for the Fibonacci numbers.",
        H("Fibonacci numbers are not 2-super-accessible"),
        Blocks(
            Node("fib-set", "The Fibonacci gap set", "fibSet", FibSet(),
                "The paper writes F = {f_n}_{n≥1} for the set of Fibonacci numbers (author-version PDF p. 2). The encoding is {d | ∃ n, 1 ≤ n ∧ d = Nat.fib n}, so the indexing starts at n=1 and both first Fibonacci occurrences are retained.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Landman)),
            Node("has-ap", "Restricted-gap arithmetic progressions", "HasAP", HasAPFormula(),
                "Definition 1 (author-version PDF p. 1) calls these “arithmetic progressions {x, x+d, x+2d, . . . , x+(k − 1)d where the gap, d, belongs S; such a progression may be called an S-ap.” The encoding uses natural-number carriers and the displayed positive start, gap membership and k-term condition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Landman)),
            Node("has-diff-seq", "Restricted-gap diffsequences", "HasDiffSeq", HasDiffSeqFormula(),
                "The source states (author-version PDF p. 2): “given a set D ⊆ Z+, a sequence x1 < x2 < . . . < xk is called a D-diffsequence if xi − xi−1 ∈ D for all i ∈ {2, . . . , k}.” The encoding adds color-class membership and a positive first entry on natural-number carriers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Landman)),
            Node("super-accessible", "Super-accessibility", "SuperAccessible", SuperAccessibleFormula(),
                "Definition 14 (author-version PDF p. 6) states: “For r ∈ Z+, a set S ⊆ Z+ is called r-super-accessible if every r-coloring of Z+, using the colors 1, 2 . . . , r, admits arbitrarily long S-aps of color 1 or arbitrarily long S-diffsequences of color j for some j ∈ {2, 3, . . . , r}.” The encoding uses positive naturals and the literal colors.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Landman)),
            Node("claim", "The published question", "claim", ClaimFormula(),
                "Section 5, question 3 (author-version PDF p. 16) asks verbatim: “Is the set of Fibonacci numbers 2-super-accessible? We know it is 2-accessible but that it is not 2-large.” The Lean claim is SuperAccessible 2 fibSet.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Landman)),
            Node("coloring", "The rotation coloring", "coloring", ColoringFormula(),
                "Color n with 2 when the fractional part of ((47+√5)/58)n is below 1/16, and with 1 otherwise. The modulus-29 phase parameter follows the published construction acknowledged in Wesley's Fibonacci accessibility work.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Wesley)),
            Node("no-color-one-ap", "No 42-term color-one Fibonacci progression", "no_color_one_ap", NoColorOneAP(),
                "Every Fibonacci-gap arithmetic progression of color 1 has fewer than 42 terms. The proof uses the period-seven residue block, a 29-term hitting lemma for large gaps, and six exact rational certificates for the small gaps.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("no-color-two-diffseq", "No three-term color-two Fibonacci diffsequence", "no_color_two_diffseq", NoColorTwoDiffSeq(),
                "From a color-two point, every Fibonacci translate advances the fractional phase by more than 1/32 without wrapping. A window of width 1/16 therefore contains no three-term color-two diffsequence.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "Refutation of 2-super-accessibility", "result", Disp(Seq(Neg, Call("claim"))),
                "The two avoidance theorems contradict the two alternatives in SuperAccessible 2 fibSet for the displayed coloring, proving the negation of the published question.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Landman),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("landman-robertson-robertson-2023-fibonacci-super-accessibility"),
                    ResolutionKind.Refuted))
        ), []));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula N() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula SetN() => Call("Set", N());
    private static Formula Fn(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula DotFn(string name, params Formula[] args)
    {
        var pieces = name.Split('.');
        Formula head = Seq(Operatorname, Grp(F.Id(pieces[0])));
        foreach (var piece in pieces.Skip(1))
            head = Seq(head, Dot, Operatorname, Grp(F.Id(piece)));
        return args.Length == 0 ? head : new Formula.Apply(head, [.. args]);
    }
    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula s) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, s);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[0]);
        for (var i = 1; i < clauses.Length; i++)
            result = Seq(result, Sp, Land, Sp, Parenthesized(clauses[i]));
        return result;
    }
    private static Formula Or(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[0]);
        for (var i = 1; i < clauses.Length; i++)
            result = Seq(result, Sp, Lor, Sp, Parenthesized(clauses[i]));
        return result;
    }
    private static Formula Imp(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Rightarrow, Sp, b);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula IfThenElse(Formula condition, Formula whenTrue, Formula whenFalse) =>
        Parenthesized(Seq(Operatorname, Grp(F.Id("if")), Sp, Parenthesized(condition), Sp,
            Operatorname, Grp(F.Id("then")), Sp, whenTrue, Sp,
            Operatorname, Grp(F.Id("else")), Sp, whenFalse));
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula TypeArrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula NatSeq() => TypeArrow(N(), N());

    private static Formula FibSet() => Disp(Eq(Fn("fibSet"), SetOf("d", N(),
        Exists("n", N(), And(Le(D(1), F.Id("n")), Eq(F.Id("d"), DotFn("Nat.fib", F.Id("n"))))))));

    private static Formula HasAPFormula()
    {
        var s = F.Id("S"); var a = F.Id("A"); var k = F.Id("k");
        var i = F.Id("i"); var x = F.Id("x"); var d = F.Id("d");
        var body = Exists("x", N(), Exists("d", N(), And(
            Le(D(1), x), Mem(d, s),
            Bind("i", N(), Imp(Lt(i, k), Mem(Add(x, Mul(i, d)), a))))));
        return Disp(Bind("S", SetN(), Bind("A", SetN(), Bind("k", N(),
            Eq(Fn("HasAP", s, a, k), body)))));
    }

    private static Formula HasDiffSeqFormula()
    {
        var s = F.Id("S"); var a = F.Id("A"); var k = F.Id("k");
        var i = F.Id("i"); var x = F.Id("x");
        var step = Imp(Lt(Add(i, D(1)), k), And(
            Lt(Fn("x", i), Fn("x", Add(i, D(1)))),
            Mem(Sub(Fn("x", Add(i, D(1))), Fn("x", i)), s)));
        var body = Exists("x", NatSeq(), And(
            Le(D(1), Fn("x", D(0))), Bind("i", N(), step),
            Bind("i", N(), Imp(Lt(i, k), Mem(Fn("x", i), a)))));
        return Disp(Bind("S", SetN(), Bind("A", SetN(), Bind("k", N(),
            Eq(Fn("HasDiffSeq", s, a, k), body)))));
    }

    private static Formula SuperAccessibleFormula()
    {
        var r = F.Id("r"); var s = F.Id("S"); var c = F.Id("c"); var n = F.Id("n");
        var k = F.Id("k"); var j = F.Id("j");
        var colorSet = (Formula color) => SetOf("n", N(), Eq(Fn("c", F.Id("n")), color));
        var admissible = Bind("n", N(), Imp(Le(D(1), n), And(
            Le(D(1), Fn("c", n)), Le(Fn("c", n), r))));
        var alternatives = Or(
            Bind("k", N(), Fn("HasAP", s, colorSet(D(1)), k)),
            Exists("j", N(), And(Le(D(2), j), Le(j, r),
                Bind("k", N(), Fn("HasDiffSeq", s, colorSet(j), k)))));
        return Disp(Bind("r", N(), Bind("S", SetN(),
            Eq(Fn("SuperAccessible", r, s),
                Bind("c", NatSeq(), Imp(admissible, alternatives))))));
    }

    private static Formula ClaimFormula() => Disp(Eq(Fn("claim"), Fn("SuperAccessible", D(2), Fn("fibSet"))));

    private static Formula ColoringFormula()
    {
        var n = F.Id("n");
        var alpha = new Formula.Fraction(Parenthesized(Seq(D(4,7), Sp, Plus, Sp, DotFn("Real.sqrt", D(5)))), D(5,8));
        var phase = DotFn("Int.fract", Mul(alpha, CastReal(n)));
        var rhs = IfThenElse(Lt(phase, new Formula.Fraction(D(1), D(1,6))), D(2), D(1));
        return Disp(Bind("n", N(), Eq(Fn("coloring", n), rhs)));
    }

    private static Formula Real() => new Formula.NamedConstant(FormulaIdentifier.Create("Real"));
    private static Formula CastReal(Formula value) => Parenthesized(Seq(DotFn("Nat.cast", value), Sp, Colon, Sp, Real()));

    private static Formula NoColorOneAP() => Disp(Seq(Neg, Fn("HasAP", Fn("fibSet"),
        SetOf("n", N(), Eq(Fn("coloring", F.Id("n")), D(1))), D(4,2))));

    private static Formula NoColorTwoDiffSeq() => Disp(Seq(Neg, Fn("HasDiffSeq", Fn("fibSet"),
        SetOf("n", N(), Eq(Fn("coloring", F.Id("n")), D(2))), D(3))));
}
