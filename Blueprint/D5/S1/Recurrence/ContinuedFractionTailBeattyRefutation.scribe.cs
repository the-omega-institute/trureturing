using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class ContinuedFractionTailBeattyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/ContinuedFractionTailBeattyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/fokkinkjoshi2025hiccup");
    private const string AsymptoticQuote =
        "Section 4, page 19: “If we assume that sₙ converges to αn + β with order O(1/n), "
        + "and if we take u to be a natural number, then α is the u-th metallic mean and "
        + "β = (vα² − α)/(α² + 1).” ";
    private const string ClaimQuote =
        "Section 4, page 19: “The generalization of Conjecture 20 then says that the rounded "
        + "down tails of the continued fraction give the Beatty sequence with slope α and offset β.” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive continued-fraction tails need not round down to their asymptotic Beatty line.",
        H("Continued-Fraction Tails and Beatty Rounding"),
        Blocks(
            Node("offset", "The asymptotic offset", "beta", BetaFormula(),
                AsymptoticQuote
                + "Here u is natural and v is real. The metallic mean is the existing "
                + "metallicValue u = (u + Real.sqrt (u² + 4))/2, with u coerced to the reals.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("tails", "Positive tails of Equation (14)", "IsTail", TailFormula(),
                "Section 4, page 19: “for constants u and v. Its tails satisfy sₙ = nu + v + n²/sₙ₊₁.” "
                + "IsTail requires this equality and positivity at every natural index n ≥ 1. "
                + "The value at zero is unrestricted; all divisions in the recurrence are real divisions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The generalized rounding assertion", "claim",
                Disp(Iff(F.Id("claim"), Parenthesized(ClaimBody()))),
                ClaimQuote + AsymptoticQuote
                + "The slope is the displayed radical. The order bound means that one real constant C "
                + "bounds the absolute error by C/n at every n ≥ 1. Floors take values in the integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("refutation", "The generalized rounding assertion is false", "result",
                Disp(new Formula.Not(Parenthesized(ClaimBody()))),
                "For u = 2 and v = 1, the slope is 1 + Real.sqrt 2 and beta 2 1 = 1/2. "
                + "A contraction on a closed set of bounded continuous functions constructs positive tails "
                + "whose error lies strictly between 1/(8n) and metallicValue 2/(4n). "
                + "At n = 1 the Beatty line has floor 2, while the recurrence gives s 1 = 3 + 1/(s 2) > 3. "
                + "Thus their floors differ. The kernel-checked settlement is this index-one case. "
                + "The Pell-index derivation below is mathematical exposition, not a separately "
                + "kernel-checked declaration. Uniqueness of positive tails and convergence of finite "
                + "continued-fraction truncations remain open.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fokkink-joshi-2025-continued-fraction-tail-beatty"),
                    ResolutionKind.Refuted)),
            Paragraph(Text(
                "For the Pell-index comparison, let r range over the natural numbers and define "
                + "integer sequences p and n by the following initial values and recurrences. "
                + "Write alpha for one plus the square root of two and x for the asymptotic line.")),
            new DocumentBlock.DisplayFormula(PellRecurrenceFormula()),
            Paragraph(Text(
                "Induction gives odd p, positive n and p squared minus eight n squared equal to one: "
                + "substitution of the recurrences preserves this difference. Both sequences strictly "
                + "increase. Eliminating p gives the second-order recurrence for n. "
                + "The integer m and the line x are defined by:")),
            new DocumentBlock.DisplayFormula(PellDefinitionsFormula()),
            Paragraph(Text(
                "The positive Pell identity gives p greater than 2n sqrt(2). Rationalizing the "
                + "difference yields the exact gap below; its denominator exceeds 8n because "
                + "p + 2n sqrt(2) exceeds 4n.")),
            new DocumentBlock.DisplayFormula(PellGapFormula()),
            Paragraph(Text(
                "The sharp bounds on the constructed tail error give the following comparison. "
                + "The last inequality uses alpha/(4n) < 1 for n at least one.")),
            new DocumentBlock.DisplayFormula(PellComparisonFormula()),
            Paragraph(Text(
                "Since m is integral, these inequalities determine both floors at every Pell index. "
                + "This is a consequence proved in prose for the constructed tails; its quantified "
                + "Lean formalization remains open.")),
            new DocumentBlock.DisplayFormula(PellFloorsFormula()))));

    private static Formula PellRecurrenceFormula()
    {
        var r = F.Id("r");
        var p = Sub("p", r);
        var n = Sub("n", r);
        return Disp(Seq(Equal(Sub("p", D(0)), D(3)), Comma, Sp,
            Equal(Sub("n", D(0)), D(1)), Comma, Quad, Sp,
            Equal(Sub("p", Add(r, D(1))), Add(Multiply(D(3), p), Multiply(D(8), n))), Comma, Quad, Sp,
            Equal(Sub("n", Add(r, D(1))), Add(p, Multiply(D(3), n)))));
    }

    private static Formula PellDefinitionsFormula()
    {
        var r = F.Id("r");
        var n = Sub("n", r);
        return Disp(Seq(Equal(Subtract(Square(Sub("p", r)), Multiply(D(8), Square(n))), D(1)),
            Comma, Quad, Sp, Equal(Sub("n", Add(r, D(2))),
                Subtract(Multiply(D(6), Sub("n", Add(r, D(1)))), n)), Comma, Quad, Sp,
            Equal(Sub("m", r), Add(n, Fraction(Add(Sub("p", r), D(1)), D(2)))), Comma, Quad, Sp,
            Equal(Sub("x", r), Add(Multiply(Alpha, n), Fraction(D(1), D(2))))));
    }

    private static Formula PellGapFormula()
    {
        var r = F.Id("r");
        var p = Sub("p", r);
        var n = Sub("n", r);
        var root = Seq(Sqrt, Grp(D(2)));
        return Disp(Seq(D(0), Sp, Lt, Sp, Subtract(Sub("m", r), Sub("x", r)), Sp, Eq, Sp,
            Fraction(Subtract(p, Multiply(Multiply(D(2), n), root)), D(2)), Sp, Eq, Sp,
            Fraction(D(1), Multiply(D(2), Parenthesized(Add(p, Multiply(Multiply(D(2), n), root))))),
            Sp, Lt, Sp, Fraction(D(1), Multiply(D(8), n))));
    }

    private static Formula PellComparisonFormula()
    {
        var r = F.Id("r");
        var n = Sub("n", r);
        var m = Sub("m", r);
        var x = Sub("x", r);
        return Disp(Seq(Subtract(m, D(1)), Sp, Lt, Sp, x, Sp, Lt, Sp, m, Sp, Lt, Sp,
            Add(x, Fraction(D(1), Multiply(D(8), n))), Sp, Lt, Sp, Sub("s", n), Sp, Lt, Sp,
            Add(x, Fraction(Alpha, Multiply(D(4), n))), Sp, Lt, Sp, Add(m, D(1))));
    }

    private static Formula PellFloorsFormula()
    {
        var r = F.Id("r");
        return Disp(Seq(Equal(Floor(Sub("s", Sub("n", r))), Sub("m", r)), Comma, Quad, Sp,
            Equal(Floor(Sub("x", r)), Subtract(Sub("m", r), D(1)))));
    }

    private static Formula Sub(string name, Formula index) => new Formula.Subscript(F.Id(name), index);

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("fokkink-joshi-tails-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula BetaFormula()
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var a = Call("metallicValue", u);
        return Disp(All([Bound("u", Naturals()), Bound("v", Reals())],
            Equal(Call("beta", u, v), Fraction(
                Subtract(Multiply(v, Square(a)), a), Add(Square(a), D(1))))));
    }

    private static Formula TailFormula()
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var s = F.Id("s");
        var n = F.Id("n");
        var recurrence = Equal(Apply(s, n), Add(Add(Multiply(Cast(n), Cast(u)), v),
            Fraction(Square(Cast(n)), Apply(s, Add(n, D(1))))));
        var body = All([Bound("n", Naturals())], Implies(Leq(D(1), n),
            And(Less(D(0), Apply(s, n)), recurrence)));
        return Disp(All([Bound("u", Naturals()), Bound("v", Reals()), Bound("s", SequenceType())],
            Iff(Call("IsTail", u, v, s), Parenthesized(body))));
    }

    private static Formula ClaimBody()
    {
        var u = F.Id("u");
        var v = F.Id("v");
        var s = F.Id("s");
        var n = F.Id("n");
        var line = Add(Multiply(Slope(u), Cast(n)), Call("beta", u, v));
        var error = new Formula.Absolute(Subtract(Apply(s, n), Parenthesized(line)));
        var bound = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("C", Reals())], All([Bound("n", Naturals())],
                Implies(Leq(D(1), n), Leq(error, Fraction(F.Id("C"), Cast(n))))));
        var rounding = All([Bound("n", Naturals())], Implies(Leq(D(1), n),
            Equal(Floor(Apply(s, n)), Floor(line))));
        return All([Bound("u", Naturals())], Implies(Leq(D(1), u),
            All([Bound("v", Reals()), Bound("s", SequenceType())],
                Implies(Call("IsTail", u, v, s), Implies(bound, rounding)))));
    }

    private static Formula Slope(Formula u) => Fraction(Add(Cast(u),
        new Formula.Apply(Seq(Operatorname, Grp(F.Id("Real")), Dot,
            Operatorname, Grp(F.Id("sqrt"))), [Add(Square(Cast(u)), D(4))])), D(2));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula SequenceType() => Seq(Naturals(), Sp, To, Sp, Reals());
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Colon, Sp, Reals()));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Apply(Formula function, Formula arg) => new Formula.Apply(function, [arg]);
    private static Formula Square(Formula value) => new Formula.Power(value, D(2));
    private static Formula Fraction(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Floor(Formula value) => Seq(Lfloor, Sp, value, Sp, Rfloor);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Subtract(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Multiply(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Implies(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
}
