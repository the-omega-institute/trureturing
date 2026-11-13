using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233164KingStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233164KingStrip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233164");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full generating series of normalized four-column eight-colour king strips.",
        H("Horizontal, vertical and both diagonal exclusions"),
        Blocks(
            Paragraph(Text("OEIS A233164, revision 8, defines literal n by four arrays with colours zero through seven. Every horizontal, vertical and both diagonal bonds exclude equal colours and colours summing to seven. There is no wraparound. The upper-left value is zero. Every occurrence of 2, 3, 4, 5 or 6 has a strictly earlier 1; every 3, 4 or 5 has a strictly earlier 2; every 4 has a strictly earlier 3, in row-major order. Colours may be absent, and no precedence condition is imposed on 7. No group action or orbit divisor enters the count.")),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "a"),
                H("An independent literal count"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finset.univ ranges over every function on the displayed finite cell domain. Fin.val gives the natural coordinate. Fin.castSucc and Fin.succ are the two endpoints in adjacent columns; Fin.mk constructs the next row with its displayed bound proof. The rank 4 times row plus column is strictly row-major. The first-cell existential is false when n is zero, so the added constant coefficient is zero. The source counting problem concerns every positive n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The complete rational formal power series"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The complementary pairs are {0,7}, {1,6}, {2,5} and {3,4}. A pair boundary with adjacent entries distinct is productive precisely when its endpoints differ. Its alternating type has first equal to third and second equal to fourth. Once 1, 2 and 3 have appeared, every legal next row preserves the productive type, with 32 colour-row continuations in the alternating type and 16 otherwise. The finite certificates verify these counts, preservation, and saturation of every two-row seed. There are 16 alternating seeds and 48 other productive seeds. The continuation induction gives a(n+2)=16 times 32 to the n plus 48 times 16 to the n for every natural n. There are 11 first rows.")),
                    Paragraph(Text("The literal Normal predicate uses strict rank 4 times row plus column. Its equivalence with the imported scanner and the arbitrary-width width_counting_bridge connects the independently defined function count to continuation. Both diagonal directions, vertical bonds and horizontal bonds are included, and boundaries are free. The initial values, natural closed form, integer recurrence and rational series are one conjunction about this count. The constant coefficient is zero solely for the series. The inverse denominator has constant coefficient one. Chang and Shrock already give the labelled proper-colouring polynomial for these underlying strips, DOI 10.1103/PhysRevE.62.4650; that polynomial is not a new result here. The normalized literal count requires the signed-lift and first-occurrence constraints stated above."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233164"),
                    ResolutionKind.Proved)))));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var h = V("h"); var p = V("p"); var q = V("q");
        var cells = Product(Call("Fin", n), Fin(4));
        Formula Cell(Formula r, Formula c) => App(a, Pair(r, c));
        Formula Bond(Formula u, Formula v) => And(Ne(u, v), Ne(Add(Val(u), Val(v)), D(7)));
        var left = Call("Fin.castSucc", j); var right = Call("Fin.succ", j);
        var next = Call("Fin.mk", Add(Val(i), D(1)), h);
        var first = Ex("i", Call("Fin", n), And(Eq(Val(i), D(0)), Eq(Cell(i, D(0)), D(0))));
        var horizontal = All("i", Call("Fin", n), All("j", Fin(3), Bond(Cell(i, left), Cell(i, right))));
        var diagonal = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(3), And(Bond(Cell(i, left), Cell(next, right)),
                Bond(Cell(i, right), Cell(next, left))))));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), D(colour))));
        var vertical = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(4), Bond(Cell(i, j), Cell(next, j)))));
        var normal = All("p", cells, And(
            Imp(Or(Eq(App(a, p), D(2)), Or(Eq(App(a, p), D(3)),
                Or(Eq(App(a, p), D(4)), Or(Eq(App(a, p), D(5)), Eq(App(a, p), D(6)))))), Earlier(1)),
            And(Imp(Or(Eq(App(a, p), D(3)), Or(Eq(App(a, p), D(4)), Eq(App(a, p), D(5)))), Earlier(2)),
                Imp(Eq(App(a, p), D(4)), Earlier(3)))));
        var predicate = Seq(LambdaLower, Sp, a, Colon, Sp, Arrow(cells, Fin(8)), Sp,
            Mapsto, Sp, Par(And(first, And(horizontal, And(And(vertical, diagonal), normal)))));
        return All("n", V("Nat"), Eq(Call("a", n),
            Call("Finset.card", Call("Finset.filter", predicate, Call("Finset.univ")))));
    }

    private static Formula ResultFormula()
    {
        var x = V("X"); var n = V("n");
        Formula A(Formula k) => Call("a", k);
        var series = Call("PowerSeries.mk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp,
            Mapsto, Sp, Par(Seq(A(n), Colon, Sp, V("Rat")))));
        var numerator = Mul(x, Add(Sub(D(1,1), Mul(D(4,6,4), x)), Mul(D(3,8,4,0), Pow(x, D(2)))));
        var denominator = Mul(Sub(D(1), Mul(D(1,6), x)), Sub(D(1), Mul(D(3,2), x)));
        var gf = Seq(Eq(series, Mul(numerator, Pow(Par(denominator), new Formula.Negate(Num(1))))),
            Sp, Name("in"), Sp, Call("PowerSeries", V("Rat")));
        var closed = All("n", V("Nat"), Imp(Lt(D(1), n),
            Eq(A(n), Mul(Pow(D(4), Sub(Mul(D(2), n), D(3))), Add(Pow(D(2), n), D(1,2))))));
        var recurrence = All("n", V("Nat"), Imp(Lt(D(3), n),
            Eq(Seq(A(n), Colon, Sp, V("Int")),
                Sub(Mul(D(4,8), A(Sub(n,D(1)))), Mul(D(5,1,2), A(Sub(n,D(2))))))));
        return And(Eq(A(D(1)),D(1,1)), And(Eq(A(D(2)),D(6,4)),
            And(Eq(A(D(3)),D(1,2,8,0)), And(closed,And(recurrence,gf)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Name(name), args);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Par(a), Sp, Times, Sp, Par(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Val(Formula a) => Call("Fin.val", a);
    private static Formula Rank(Formula p) => Add(Mul(D(4), Val(Call("Prod.fst", p))), Val(Call("Prod.snd", p)));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Or(Formula a, Formula b) => Seq(Par(a), Sp, Lor, Sp, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(Par(a), b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
