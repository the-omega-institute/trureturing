using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233175PairStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233175PairStrip.";
    private const string Note = "D5/L/Automata/hardin2013a233175";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for complementary-pair exclusion on a two-row strip.",
        H("Six-colour complementary-pair exclusion"),
        Blocks(
            Paragraph(Text("The colours are 0 through 5. Consecutive columns have all four possible bonds; there is no bond within a column. A bond forbids equal colours and complementary colours whose sum is five. The distinguished upper-left cell has colour zero. In row-major order every 2, 3 and 4 has an earlier 1, and every 3 has an earlier 2. The empty-strip coefficient is zero. OEIS A233175, revision 7, gives this NAME and labels the displayed generating function a conjecture of Colin Barker.")),
            Def("seen", "Seen", "Two seen-colour flags", Eq(V("Seen"), Product(V("Bool"), V("Bool"))),
                "The first flag records whether colour one has occurred; the second records colour two."),
            Def("col", "Col", "A column", Eq(V("Col"), Arrow(Fin(2), Fin(6))),
                "A column is an ordered function on the two row indices."),
            Def("allowed", "allowed", "The next colour", AllowedFormula(),
                "The two implications impose exactly the required earlier occurrences."),
            Def("advance", "advance", "Updating the flags", AdvanceFormula(),
                "A flag changes to true when its colour occurs and otherwise retains its value."),
            Def("good", "good", "Scanning a word", GoodFormula(),
                "The empty word is accepted. A nonempty word is accepted exactly when its first colour is allowed and its tail is accepted with the updated flags."),
            Def("finish", "finish", "Final flags of a word", FinishFormula(),
                "The empty word retains its initial flags. For a nonempty word the first colour updates the flags before the tail is scanned."),
            Def("pair", "pair", "Complementary-pair labels", PairFormula(),
                "The three labels have fibres {0,5}, {1,4} and {2,3}. A legal bond joins different fibres."),
            Def("pairs", "pairs", "The two boundary labels", PairsFormula(),
                "Only the complementary-pair labels of the preceding column affect future bonds."),
            Def("a", "a", "The literal filtered count", CountFormula(),
                "The finite set contains all arrays on Fin 2 times Fin n, filtered by the displayed predicate. The rank r*n+j is the row-major order. The first-entry existential also makes a(0)=0."),
            Def("step", "step", "One-column continuation", StepFormula(),
                "The sum ranges over all thirty-six columns. Both new colours must avoid both preceding pair labels and satisfy their respective seen-colour flags."),
            Def("v", "v", "Continuation vectors", VectorFormula(),
                "The parameter q specifies the final top-row flags. The current flags are t and b. At length zero only t=q is required. A positive continuation appends one column."),
            Def("total", "total", "Closing the row-major boundary", TotalFormula(),
                "The first top colour is zero. The final top flags q are also the initial bottom flags, since all top-row cells precede the bottom row. Summing over q selects the unique final top record."),
            Thm("finite-certificate", "finite_certificate", "A finite continuation identity", CertificateFormula(),
                "The seven-step identity holds on all 576 states. The listed scalar values concern continuation lengths zero through six. Linearity propagates the identity to every continuation length."),
            Thm("result", "result", "Barker's generating function", ResultFormula(),
                "The literal filtered count equals total(v(n-1)) at every positive width, by decomposition into the first column and its tail. The seven-step identity has polynomial z^2*(z^3-12*z^2+128)*(z^2-4*z-16). The listed initial values eliminate the extra factor for the scalar count and yield a(n)=12*a(n-1)-128*a(n-3) for n at least five. Comparing every power-series coefficient gives the identity. The cast from natural counts to integers is taken before forming the series."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula AllowedFormula()
    {
        var s = V("s"); var c = V("c");
        var body = And(Imp(Or(Eq(c, D(2)), Or(Eq(c, D(3)), Eq(c, D(4)))), Eq(Proj(s, 1), V("true"))),
            Imp(Eq(c, D(3)), Eq(Proj(s, 2), V("true"))));
        return All("s", V("Seen"), All("c", Fin(6), Iff(Call("allowed", s, c), body)));
    }

    private static Formula AdvanceFormula()
    {
        var s = V("s"); var c = V("c");
        Formula Flag(byte j) => Seq(Proj(s, j), Sp, Operatorname, Grp(V("or")), Sp,
            Call("decide", Eq(c, D(j))));
        return All("s", V("Seen"), All("c", Fin(6), Eq(Call("advance", s, c), Pair(Flag(1), Flag(2)))));
    }

    private static Formula PairFormula()
    {
        var c = V("c");
        var vector = Seq(OpenBracket, D(0), Comma, D(1), Comma, D(2), Comma, D(2), Comma,
            D(1), Comma, D(0), CloseBracket);
        return All("c", Fin(6), Eq(Call("pair", c), App(vector, c)));
    }

    private static Formula GoodFormula()
    {
        var s = V("s"); var f = V("f"); var n = V("n");
        return new Formula.Aligned([
            All("s", V("Seen"), All("f", Arrow(Fin(0), Fin(6)),
                Iff(Call("good", s, f), V("True")))),
            All("n", V("Nat"), All("s", V("Seen"),
                All("f", Arrow(Call("Fin", Add(n, D(1))), Fin(6)),
                    Iff(Call("good", s, f), And(Call("allowed", s, App(f, D(0))),
                        Call("good", Call("advance", s, App(f, D(0))), Call("Fintail", f)))))))]);
    }

    private static Formula FinishFormula()
    {
        var s = V("s"); var f = V("f"); var n = V("n");
        return new Formula.Aligned([
            All("s", V("Seen"), All("f", Arrow(Fin(0), Fin(6)),
                Eq(Call("finish", s, f), s))),
            All("n", V("Nat"), All("s", V("Seen"),
                All("f", Arrow(Call("Fin", Add(n, D(1))), Fin(6)),
                    Eq(Call("finish", s, f),
                        Call("finish", Call("advance", s, App(f, D(0))), Call("Fintail", f))))))]);
    }

    private static Formula PairsFormula()
    {
        var c = V("c");
        return All("c", V("Col"), Eq(Call("pairs", c),
            Pair(Call("pair", App(c, D(0))), Call("pair", App(c, D(1))))));
    }

    private static Formula Rank(Formula p, Formula n) =>
        Add(Mul(Call("val", Proj(p, 1)), n), Call("val", Proj(p, 2)));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var j = V("j"); var r = V("r"); var s = V("s");
        var p = V("p"); var q = V("q");
        var cells = Product(Fin(2), Call("Fin", n));
        var first = Ex("j", Call("Fin", n), And(Eq(Call("val", j), D(0)),
            Eq(App(a, Pair(D(0), j)), D(0))));
        var here = App(a, Pair(r, j));
        var next = App(a, Pair(s, Call("Finmk", Add(Call("val", j), D(1)))));
        var bonds = All("j", Call("Fin", n), Imp(Lt(Add(Call("val", j), D(1)), n),
            All("r", Fin(2), All("s", Fin(2), And(Ne(here, next),
                Ne(Add(Call("val", here), Call("val", next)), D(5)))))));
        Formula Earlier(byte c) => Ex("q", cells, And(Lt(Rank(q, n), Rank(p, n)), Eq(App(a, q), D(c))));
        var normal = All("p", cells, And(
            Imp(Or(Eq(App(a, p), D(2)), Or(Eq(App(a, p), D(3)), Eq(App(a, p), D(4)))), Earlier(1)),
            Imp(Eq(App(a, p), D(3)), Earlier(2))));
        var predicate = Seq(LambdaLower, Sp, a, Colon, Sp, Arrow(cells, Fin(6)), Sp,
            Mapsto, Sp, Parenthesized(And(first, And(bonds, normal))));
        var boards = Call("Finsetfilter", predicate, V("Finsetuniv"));
        return All("n", V("Nat"), Eq(Call("a", n), Call("Finsetcard", boards)));
    }

    private static Formula StateFunction() => Arrow(V("Seen"), Arrow(V("Seen"),
        Arrow(V("Seen"), Arrow(Product(Fin(3), Fin(3)), V("Int")))));

    private static Formula StepFormula()
    {
        var w = V("w"); var q = V("q"); var t = V("t"); var b = V("b"); var p = V("p");
        var c = V("c"); var r = V("r");
        var edge = All("r", Fin(2), And(Ne(Call("pair", App(c, r)), Proj(p, 1)),
            Ne(Call("pair", App(c, r)), Proj(p, 2))));
        var cond = And(edge, And(Call("allowed", t, App(c, D(0))), Call("allowed", b, App(c, D(1)))));
        var next = App(w, q, Call("advance", t, App(c, D(0))),
            Call("advance", b, App(c, D(1))), Call("pairs", c));
        var sum = SumOver("c", V("Col"), Conditional(cond, next, D(0)));
        return All("w", StateFunction(), States(Eq(Call("step", w, q, t, b, p), sum)));
    }

    private static Formula VectorFormula()
    {
        var k = V("k"); var q = V("q"); var t = V("t"); var b = V("b"); var p = V("p");
        return new Formula.Aligned([
            States(Eq(Call("v", D(0), q, t, b, p), Conditional(Eq(t, q), D(1), D(0)))),
            All("k", V("Nat"), States(Eq(Call("v", Add(k, D(1)), q, t, b, p),
                Call("step", Call("v", k), q, t, b, p))))]);
    }

    private static Formula TotalFormula()
    {
        var w = V("w"); var c = V("c"); var q = V("q");
        var sum = SumOver("c", V("Col"), SumOver("q", V("Seen"), Conditional(
            And(Eq(App(c, D(0)), D(0)), Call("allowed", q, App(c, D(1)))),
            App(w, q, Pair(V("false"), V("false")), Call("advance", q, App(c, D(1))), Call("pairs", c)), D(0))));
        return All("w", StateFunction(), Eq(Call("total", w), sum));
    }

    private static Formula CertificateFormula()
    {
        var q = V("q"); var t = V("t"); var b = V("b"); var p = V("p");
        Formula Term(byte k) => Call("v", D(k), q, t, b, p);
        var vector = States(Eq(Term(7), Add(Add(Sub(Sub(Mul(D(1,6), Term(6)),
            Mul(D(3,2), Term(5))), Mul(D(3,2,0), Term(4))), Mul(D(5,1,2), Term(3))),
            Mul(D(2,0,4,8), Term(2)))));
        int[] values = [3,8,80,800,8576,92672,1009664];
        Formula initial = Eq(Call("total", Call("v", D(6))), Number(values[6]));
        for (byte k = 6; k > 0; --k)
            initial = And(Eq(Call("total", Call("v", D((byte)(k-1)))), Number(values[k-1])), initial);
        return And(vector, initial);
    }

    private static Formula ResultFormula()
    {
        var x = V("X"); var n = V("n");
        var left = Mul(Mul(Sub(D(1), Mul(D(4), x)),
            Sub(Sub(D(1), Mul(D(8), x)), Mul(D(3,2), Pow(x, D(2))))),
            Call("PowerSeriesmk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp, Mapsto, Sp,
                Cast(Call("a", n)))));
        var right = Mul(x, Add(Sub(Sub(D(3), Mul(D(2,8), x)), Mul(D(1,6), Pow(x, D(2)))),
            Mul(D(2,2,4), Pow(x, D(3)))));
        return Seq(Eq(left, right), Sp, TextFormula("in"), Sp, Call("PowerSeries", V("Int")));
    }

    private static Formula States(Formula body) => All("q", V("Seen"), All("t", V("Seen"),
        All("b", V("Seen"), All("p", Product(Fin(3), Fin(3)), body))));
    private static Formula Number(int n) => Seq(n.ToString(System.Globalization.CultureInfo.InvariantCulture).Select(c => D((byte)(c-'0'))).ToArray());
    private static Formula TextFormula(string s) => Seq(Operatorname, Grp(V(s)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(TextFormula(name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Proj(Formula a, byte i) => Call("proj", a, D(i));
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(TextFormula("if"), Sp, Parenthesized(condition), Sp, TextFormula("then"), Sp,
            yes, Sp, TextFormula("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
