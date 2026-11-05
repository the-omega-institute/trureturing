using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class HardinWidthTwoRecurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/AdmissibleWords/HardinWidthTwoRecurrence.";
    private const string Note = "D5/L/Automata/hardin2012a206981";
    private const string NameQuote = "Number of n X 2 0..1 arrays avoiding the patterns 0 1 0 or 1 0 1 in any row, column, diagonal or antidiagonal.";
    private const string FormulaQuote = "Empirical: a(n) = 2*a(n-1) + 2*a(n-2) - a(n-3). G.f.: -4*x*(-1-2*x+x^2) / ( (1+x)*(x^2-3*x+1) ).";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's width-two array recurrence and offset-one generating function.",
        H("Hardin's width-two pattern-avoiding arrays"),
        Blocks(
            Paragraph(Text("OEIS A206981, revision 17, NAME: \"" + NameQuote + "\" The entry has no page numbers. A cell has row index in Fin n and column index in Fin 2; false represents 0 and true represents 1. Rectangles have no wraparound, and all forbidden triples are contiguous.")),
            Definition("Forbidden", "The two forbidden triples",
                ForbiddenDefinition(),
                "OEIS A206981, revision 17, NAME: \"" + NameQuote + "\" The entry has no page numbers. The two displayed Boolean triples represent its patterns 0 1 0 and 1 0 1."),
            Definition("StraightTriple", "Contiguous triples in the four directions",
                StraightDefinition(),
                "OEIS A206981, revision 17, NAME: \"" + NameQuote + "\" The entry has no page numbers. The four direction steps are (0,1), (1,0), (1,1) and (1,-1). Coordinates are cast to Int before adding a step; all three cells remain in the finite rectangle. Reversing a step preserves both forbidden patterns."),
            Definition("Avoids", "The source array predicate",
                AvoidsDefinition(),
                "OEIS A206981, revision 17, NAME: \"" + NameQuote + "\" The entry has no page numbers. Avoids checks every triple in the four listed directions on the actual array."),
            Definition("a", "The actual array count",
                CountDefinition(),
                "OEIS A206981, revision 17, NAME: \"" + NameQuote + "\" The entry has no page numbers. The number of arrays is the cardinality of the subtype of finite binary arrays satisfying Avoids. The empty rectangle has its usual array count; the generating series begins at height one."),
            Definition("gf", "The offset-one ordinary generating series",
                SeriesDefinition(),
                "OEIS A206981, revision 17, OFFSET: \"1,1\". The entry has no page numbers. Thus gf is an integer formal power series whose constant coefficient is zero and whose coefficient at every positive n is the integer cast of a n. No convergence assumption is used."),
            Definition("claim", "The first FORMULA assertion",
                IffOf(V("claim"), ClaimBody()),
                "OEIS A206981, revision 17, first FORMULA: \"" + FormulaQuote + "\" The entry has no page numbers. The recurrence starts at n ≥ 4; lagged indices use Nat subtraction and count values are cast to Int. The generating-function denominator has constant coefficient one. Multiplying out (1+x)*(x^2-3*x+1) and the printed numerator gives exactly the displayed formal-series identity."),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The recurrence and generating function"),
                StatementSource.FromAuthor(Disp(ClaimBody())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Width two excludes horizontal and diagonal triples, leaving two independent legal columns. A positive-length column is determined by its first bit and its adjacent XOR switches. A forbidden triple occurs exactly when two consecutive switches are true. The existing admissible-word enumeration therefore gives 2 F(n+1) columns and 4 F(n+1)^2 arrays for each n ≥ 1. Mathlib's Fin.partialSum inverse laws reconstruct the bits from the switches. The Fibonacci recurrence yields the signed order-three recurrence by polynomial algebra. Comparing formal-series coefficients, with initial counts 4, 16 and 36, proves the generating-function identity."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin-a206981-width-two-recurrence"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    private static Formula ForbiddenDefinition()
    {
        var x = V("x"); var y = V("y"); var z = V("z");
        var body = OrOf(AndOf(Eq(x, V("false")), Eq(y, V("true")), Eq(z, V("false"))),
            AndOf(Eq(x, V("true")), Eq(y, V("false")), Eq(z, V("true"))));
        return All("x", V("Bool"), All("y", V("Bool"), All("z", V("Bool"),
            IffOf(Call("Forbidden", x, y, z), body))));
    }

    private static Formula AvoidsDefinition()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q"); var r = V("r");
        var triple = Imp(Call("StraightTriple", p, q, r),
            NotOf(Call("Forbidden", Entry(a, p), Entry(a, q), Entry(a, r))));
        var body = All("p", CellType(n), All("q", CellType(n), All("r", CellType(n), triple)));
        return All("n", V("Nat"), All("A", ArrayType(n), IffOf(Call("Avoids", a), body)));
    }

    private static Formula CountDefinition()
    {
        var n = V("n");
        var arrays = Seq(OpenBrace, V("A"), Colon, Sp, ArrayType(n), Sp, Mid, Sp,
            Call("Avoids", V("A")), CloseBrace);
        return All("n", V("Nat"), Eq(Call("a", n), App(Q("Nat", "card"), arrays)));
    }

    private static Formula SeriesDefinition()
    {
        var coefficient = Call("ite", Parenthesized(Eq(V("n"), D(0))), D(0),
            Cast(Call("a", V("n")), V("Int")));
        return Eq(V("gf"), App(Q("PowerSeries", "mk"), Lam("n", V("Nat"), coefficient)));
    }

    private static Formula StraightDefinition()
    {
        var n = V("n"); var p = V("p"); var q = V("q"); var r = V("r");
        var dr = V("dr"); var dc = V("dc");
        var directions = OrOf(AndOf(Eq(dr, D(0)), Eq(dc, D(1))),
            AndOf(Eq(dr, D(1)), Eq(dc, D(0))),
            AndOf(Eq(dr, D(1)), Eq(dc, D(1))),
            AndOf(Eq(dr, D(1)), Eq(dc, new Formula.Negate(D(1)))));
        var body = Ex("dr", V("Int"), Ex("dc", V("Int"), AndOf(directions,
            Eq(Coordinate(q, 1), PlusOf(Coordinate(p, 1), dr)),
            Eq(Coordinate(r, 1), PlusOf(Coordinate(q, 1), dr)),
            Eq(Coordinate(q, 2), PlusOf(Coordinate(p, 2), dc)),
            Eq(Coordinate(r, 2), PlusOf(Coordinate(q, 2), dc)))));
        return All("n", V("Nat"), All("p", CellType(n), All("q", CellType(n),
            All("r", CellType(n), IffOf(Call("StraightTriple", p, q, r), body)))));
    }

    private static Formula ClaimBody()
    {
        var n = V("n");
        Formula Count(Formula index) => Cast(Call("a", index), V("Int"));
        var recurrence = All("n", V("Nat"), Imp(Seq(D(4), Sp, Leq, Sp, n),
            Eq(Count(n), MinusOf(PlusOf(TimesOf(D(2), Count(MinusOf(n, D(1)))),
                TimesOf(D(2), Count(MinusOf(n, D(2))))), Count(MinusOf(n, D(3)))))));
        var x = Q("PowerSeries", "X");
        var denominator = PlusOf(MinusOf(MinusOf(D(1), TimesOf(D(2), x)),
            TimesOf(D(2), Pow(x, D(2)))), Pow(x, D(3)));
        var numerator = MinusOf(PlusOf(TimesOf(D(4), x), TimesOf(D(8), Pow(x, D(2)))),
            TimesOf(D(4), Pow(x, D(3))));
        return AndOf(recurrence, Eq(TimesOf(V("gf"), Parenthesized(denominator)), numerator));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(V(owner), Dot, V(name)));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Seq(Operatorname, Grp(V(name))), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Arr(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula CellType(Formula n) => Seq(Call("Fin", n), Sp, Times, Sp, Call("Fin", D(2)));
    private static Formula ArrayType(Formula n) => Arr(Call("Fin", n), Arr(Call("Fin", D(2)), V("Bool")));
    private static Formula Projection(Formula p, byte i) => Seq(p, Dot, D(i));
    private static Formula Coordinate(Formula p, byte i) => Cast(Call("val", Projection(p, i)), V("Int"));
    private static Formula Entry(Formula a, Formula p) => App(a, Projection(p, 1), Projection(p, 2));
    private static Formula Cast(Formula a, Formula t) => Parenthesized(Seq(a, Colon, Sp, t));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Iff, Sp, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula NotOf(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula PlusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula MinusOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula TimesOf(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula t, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula t, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, t, Comma, Sp, Parenthesized(body));
    private static Formula Lam(string name, Formula t, Formula body) => Parenthesized(Seq(LambdaLower, Sp, V(name), Colon, Sp, t, Sp, Mapsto, Sp, body));
    private static Formula AndOf(params Formula[] items) => Join(items, Land);
    private static Formula OrOf(params Formula[] items) => Join(items, Lor);
    private static Formula Join(Formula[] items, Formula op)
    {
        var result = items[^1];
        for (var i = items.Length - 2; i >= 0; i--) result = Seq(Parenthesized(items[i]), Sp, op, Sp, Parenthesized(result));
        return result;
    }
}
