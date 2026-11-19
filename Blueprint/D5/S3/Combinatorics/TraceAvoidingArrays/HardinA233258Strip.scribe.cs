using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233258StripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233258Strip.";
    private const string LeanPrefix = "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233258Strip.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233258");
    private static DocumentBlock Resolution(string name, string title, Formula formula) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233258"), ResolutionKind.Proved));

    private static DocumentBlock Node(string name, string title, Formula formula, bool theorem,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(title + "."))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hardin's recurrence and Barker's generating function for literal three-row colourings.",
        H("Three-row complementary-pair exclusion"),
        Blocks(
            Paragraph(Text("Cells are Fin 3 times Fin n, with colour set Fin 6. A bond "
                + "joins cells in consecutive columns when their row indices are equal "
                + "or the old row is one greater than the new row. Each bond excludes "
                + "equal colours and colours summing to five. The top left colour is "
                + "zero; first occurrences obey the strict row-major rank r*n+j, "
                + "as defined by HardinA233176Ladder.normal.")),
            Node("Legal", "Literal array conditions", LegalFormula(), false),
            Node("a", "The literal filtered array count", CountFormula(), false, true),
            Node("counting_bridge", "The canonical-form counting bridge", BridgeFormula(), true),
            Paragraph(Text("The beta-label identifies {0,5}, {1,4} and {2,3}. The "
                + "canonical first-occurrence theorems apply to the cells with their "
                + "row-major linear order. A canonical pattern using k labels has "
                + "2^(3*n-k) normalized lifts. At width at least two a proper pattern "
                + "uses two or three labels and its relabelling orbit has six members. "
                + "When a label is omitted, consecutive rows in each column have a "
                + "common neighbour in an adjacent column, forcing equality. Every "
                + "column is constant and the two labels alternate. There is exactly "
                + "one canonical pattern of this kind. If C counts canonical proper "
                + "patterns, L=6*C and a=2^(3*n-3)*(C+1), yielding the bridge.")),
            Node("finite_certificate", "The width-six recurrence instance", RecurrenceFormula(null), true),
            Resolution("result", "The recurrence and exact integer power-series identity",
                And(RecurrenceFormula(V("n")), SeriesFormula())),
            Paragraph(Text("Scaling L(n)+6 by 8^n multiplies the coefficient at lag j "
                + "by 8^j, giving coefficients 48,-448,1024. The index n+6 covers "
                + "every width at least six. The initial counts at widths zero through "
                + "five are 0,11,136,4672,166400,6049792. Coefficient comparison in "
                + "PowerSeries Int gives Barker's identity; its denominator has "
                + "constant coefficient one. The width-one count is taken directly "
                + "from the literal finite filter.")))));

    private static Formula BridgeFormula()
    {
        var n = V("n");
        return All("n", Q("Nat"), Imp(Le(D(2), n), Eq(
            Mul(Num(48), Typed(Own("a", n), Q("Int"))),
            Mul(Power(Typed(D(8), Q("Int")), n),
                Add(Typed(Call("D5.S3.Combinatorics.TraceAvoidingArrays."
                    + "HardinA233258PairTransfer.L", n), Q("Int")), D(6))))));
    }
    private static Formula RecurrenceFormula(Formula? n)
    {
        Formula A(int i) => Typed(Own("a", n is null ? Num(i) : Add(n, Num(i))), Q("Int"));
        var equation = Eq(A(6), Add(Sub(Mul(Num(48), A(5)), Mul(Num(448), A(4))),
            Mul(Num(1024), A(3))));
        return n is null ? equation : All("n", Q("Nat"), equation);
    }
    private static Formula SeriesFormula()
    {
        var x = Typed(Q("PowerSeries.X"), Call("PowerSeries", Q("Int")));
        Formula P(int i) => Power(x, Num(i));
        var series = Call("PowerSeries.mk", Fn("n", Q("Nat"),
            Typed(Own("a", V("n")), Q("Int"))));
        var denominator = Mul(Sub(D(1), Mul(D(8), x)),
            Add(Sub(D(1), Mul(Num(40), x)), Mul(Num(128), P(2))));
        var numerator = Mul(x, Add(Sub(Add(Sub(Num(11), Mul(Num(392), x)),
            Mul(Num(3072), P(2))), Mul(Num(8192), P(3))), Mul(Num(16384), P(4))));
        return Eq(Mul(denominator, series), numerator);
    }
    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(3)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(3))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = Or(Eq(r, s), Eq(Val(r), Add(Val(s), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(3)), All("s", Fin(D(3)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Eq(Own("Legal", a), Parenthesized(And(first, And(bonds,
                Call("D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.normal", a)))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(3)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Parenthesized(Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)),
                Typed(Q("Finset.univ"), Call("Finset", arrays)))))));
    }

    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { NamePart(part) } : new[] { Dot, NamePart(part) }).ToArray());
    private static Formula NamePart(string name)
    {
        var words = name.Split('_');
        Formula result = V(words[^1]);
        for (var i = words.Length - 2; i >= 0; --i)
            result = Seq(V(words[i]), Underscore, Grp(result));
        return Seq(Operatorname, Grp(result));
    }
    private static Formula Own(string name, params Formula[] args) =>
        Call(LeanPrefix + name, args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula x, Formula type) =>
        Parenthesized(Seq(x, Colon, Sp, type));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
}
