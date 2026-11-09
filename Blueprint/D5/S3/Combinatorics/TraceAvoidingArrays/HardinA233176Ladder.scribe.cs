using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233176LadderDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233176Ladder.";
    private const string LeanPrefix =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233176Ladder.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Automata/hardin2013a233176");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's integer generating function for normalized three-row six-colour ladders.",
        H("Three-row complementary-pair exclusion"),
        Blocks(
            Paragraph(Text(
                "An array is a function from Fin 3 times Fin n to Fin 6. The first cell "
                + "has colour zero. Bonds join cells in consecutive columns whose row "
                + "indices differ by at most one. Each bond excludes equal colours and "
                + "colours summing to five. Row-major order scans every cell of row zero "
                + "before row one, and every cell of row one before row two. The strict "
                + "rank is Fin.val(row)*n+Fin.val(column). Fin.val is the explicit natural "
                + "coercion throughout. Nat.div denotes natural quotient division and "
                + "Nat.mod denotes its nonnegative remainder.")),
            Def("normal", "normal", "Row-major normalization", NormalFormula(),
                "Every 2, 3 or 4 has a strictly earlier 1; every 3 has a strictly earlier "
                + "2. The existential cell has the same typed finite domain as the "
                + "current cell. Equal-rank cells cannot serve as predecessors."),
            Def("legal", "Legal", "Literal array conditions", LegalFormula(),
                "The first-cell existential is false at width zero. The two natural "
                + "inequalities on row values express absolute row difference at most "
                + "one. The next column is Fin.mk (j.val+1) h, retaining its bound proof."),
            Def("count", "a", "The literal filtered count", CountFormula(),
                "Finset.univ ranges over all arrays, and the filter applies Legal "
                + "literally. Thus a(0)=0. The positive-width coefficients begin "
                + "11,80,2688,78336.", true),
            Thm("certificate", "finite_certificate", "Initial coefficients",
                CertificateFormula(),
                "The existing scanner consists of "
                + "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.Seen, "
                + "allowed, advance, good and finish. Its records correspond to levels "
                + "0,1,2 according to which of colours one and two has been seen. "
                + "The final top record starts the middle row, and the final middle "
                + "record starts the bottom row. Five ordered records and the preceding "
                + "three pair labels give 168 states in 21 classes. Finite continuation "
                + "vectors determine the displayed coefficients."),
            Thm("result", "result", "Barker's generating function", ResultFormula(),
                "The column transfer has 159 different nonzero state transitions. "
                + "Its continuation vectors satisfy an order-eleven relation. Dividing "
                + "the corresponding annihilating polynomial by "
                + "z^4-32*z^3-64*z^2+3072*z-8192 gives "
                + "z^7-16*z^6-256*z^5+3072*z^4+20480*z^3-98304*z^2-524288*z. "
                + "The initial coefficients force the order-four residual to vanish "
                + "from index six onward. Coefficient comparison gives the displayed "
                + "identity. The natural array counts are cast to integers before "
                + "PowerSeries.mk is applied."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula,
        string prose, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source)
                : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static DocumentBlock Thm(string id, string name, string title, Formula formula,
        string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula NormalFormula()
    {
        var n = V("n"); var a = V("A"); var p = V("p"); var q = V("q");
        var cells = Product(Fin(D(3)), Fin(n));
        Formula Rank(Formula x) => Add(Mul(Val(Call("Prod.fst", x)), n),
            Val(Call("Prod.snd", x)));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), Typed(D(colour), Fin(D(6))))));
        var current = App(a, p);
        var condition = All("p", cells, And(
            Imp(Or(Eq(current, Typed(D(2), Fin(D(6)))),
                Or(Eq(current, Typed(D(3), Fin(D(6)))),
                    Eq(current, Typed(D(4), Fin(D(6)))))), Earlier(1)),
            Imp(Eq(current, Typed(D(3), Fin(D(6)))), Earlier(2))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Iff(Own("normal", a), condition)));
    }

    private static Formula LegalFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j");
        var r = V("r"); var s = V("s"); var h = V("h");
        var cells = Product(Fin(D(3)), Fin(n));
        var first = Ex("j", Fin(n),
            And(Eq(Val(j), D(0)), Eq(App(a, Pair(Typed(D(0), Fin(D(3))), j)),
                Typed(D(0), Fin(D(6))))));
        var adjacent = And(Le(Val(r), Add(Val(s), D(1))),
            Le(Val(s), Add(Val(r), D(1))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Typed(Call("Fin.mk", Add(Val(j), D(1)), h), Fin(n))));
        var bonds = All("j", Fin(n), All("h", Lt(Add(Val(j), D(1)), n),
            All("r", Fin(D(3)), All("s", Fin(D(3)), Imp(adjacent,
                And(Ne(here, next), Ne(Add(Val(here), Val(next)), D(5))))))));
        return All("n", Q("Nat"), All("A", Arrow(cells, Fin(D(6))),
            Iff(Own("Legal", a), And(first, And(bonds, Own("normal", a))))));
    }

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A");
        var arrays = Arrow(Product(Fin(D(3)), Fin(n)), Fin(D(6)));
        return All("n", Q("Nat"), Eq(Own("a", n), Call("Finset.card",
            Call("Finset.filter", Fn("A", arrays, Own("Legal", a)), Q("Finset.univ")))));
    }

    private static Formula CertificateFormula()
    {
        long[] values = [0,11,80,2688,78336,2469888,76447744,2385772544,
            74291609600,2315406802944,72144847372288,2248141575290880];
        Formula Item(int i) => Eq(Typed(Own("a", Number(i)), Q("Int")), Number(values[i]));
        Formula result = Item(values.Length - 1);
        for (var i = values.Length - 2; i >= 0; --i) result = And(Item(i), result);
        return result;
    }

    private static Formula ResultFormula()
    {
        var x = Q("PowerSeries.X"); var n = V("n");
        Formula Term(long c, byte k) => Mul(Number(c), Power(x, D(k)));
        var denominator = Mul(Sub(D(1), Mul(D(8), x)),
            Add(Sub(Sub(D(1), Mul(D(2,4), x)), Term(256, 2)), Term(1024, 3)));
        var numerator = Sub(Add(Sub(Sub(D(1,1), Mul(D(2,7,2), x)), Term(576, 2)),
            Term(20992, 3)), Term(53248, 4));
        var series = Call("PowerSeries.mk", Fn("n", Q("Nat"),
            Typed(Own("a", n), Q("Int"))));
        return Eq(Typed(Mul(denominator, series), Call("PowerSeries", Q("Int"))),
            Mul(x, numerator));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Q(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula Own(string name, params Formula[] args) =>
        App(Q(LeanPrefix + name), args);
    private static Formula Call(string name, params Formula[] args) => App(Q(name), args);
    private static Formula App(Formula f, params Formula[] args) =>
        new Formula.Apply(f, [.. args]);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Fin(Formula n) => Call("Fin", n);
    private static Formula Val(Formula x) => Call("Fin.val", x);
    private static Formula Number(long n) => Num(n);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Product(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Typed(Formula a, Formula b) =>
        Parenthesized(Seq(a, Colon, Sp, b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Fn(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, body));
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Subtract, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
}
