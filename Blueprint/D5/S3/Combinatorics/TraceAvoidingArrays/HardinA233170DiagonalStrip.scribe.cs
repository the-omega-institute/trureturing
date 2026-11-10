using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233170DiagonalStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233170DiagonalStrip.";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Automata/hardin2013a233170");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full generating series of normalized four-column six-colour arrays.",
        H("Horizontal and both diagonal exclusions"),
        Blocks(
            Paragraph(Text("OEIS A233170, revision 10, defines literal n by four arrays with colours zero through five. Every horizontal bond and both diagonals between consecutive rows exclude equal colours and colours summing to five. Vertical bonds and wraparound are unconstrained. The upper-left value is zero. Every occurrence of 2, 3 or 4 has a strictly earlier 1, and every 3 has a strictly earlier 2, in row-major order. Colours may be absent. No group action or orbit divisor enters the count.")),
            Describe.Lean(DescribeId.Create("count"), DeclarationHandle.Create(Prefix + "a"),
                H("An independent literal count"), StatementSource.FromAuthor(Disp(CountFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Finset.univ ranges over every function on the displayed finite cell domain. Fin.val gives the natural coordinate. Fin.castSucc and Fin.succ are the two endpoints in adjacent columns; Fin.mk constructs the next row with its displayed bound proof. The rank 4 times row plus column is strictly row-major. The first-cell existential is false when n is zero, so the added constant coefficient is zero. The source counting problem concerns every positive n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The complete rational formal power series"), StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The private finite_certificate verifies preservation of valid boundary states, the first two continuation weights and the next-step identity, and first-row aggregation totals 10, 800 and 78336. The private continuation_recurrence proves, by induction for every continuation length, the recurrence with coefficients 128, -2816 and 16384. The literal counting bridge transports it to a(n+4)=128 a(n+3)-2816 a(n+2)+16384 a(n+1) for every natural n. Coefficient comparison retains the numerator, and formal inversion is valid because the denominator has constant coefficient one. Thus the identity includes every positive height and the initial coefficients, rather than only an eventual recurrence.")),
                    Paragraph(Text("The scanner Seen, good and finish is reused from HardinA233175PairStrip. The width-independent widthNormal, widthLegal, widthStep, widthV, widthTotal and width_counting_bridge, together with colour_bond_iff, are reused from HardinA233251TriangleStrip. Pair labels are BooleanRankThreeK4.beta, with fibres {0,5}, {1,4}, {2,3}. These reused results supply the literal transfer interface; the four-column continuation certificate and its unbounded induction supply the new combinatorial content. The assertion is about finite combinatorial counts and rational formal series. It makes no claim of global priority."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233170"),
                    ResolutionKind.Proved)))));

    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var h = V("h"); var p = V("p"); var q = V("q");
        var cells = Product(Call("Fin", n), Fin(4));
        Formula Cell(Formula r, Formula c) => App(a, Pair(r, c));
        Formula Bond(Formula u, Formula v) => And(Ne(u, v), Ne(Add(Val(u), Val(v)), D(5)));
        var left = Call("Fin.castSucc", j); var right = Call("Fin.succ", j);
        var next = Call("Fin.mk", Add(Val(i), D(1)), h);
        var first = Ex("i", Call("Fin", n), And(Eq(Val(i), D(0)), Eq(Cell(i, D(0)), D(0))));
        var horizontal = All("i", Call("Fin", n), All("j", Fin(3), Bond(Cell(i, left), Cell(i, right))));
        var diagonal = All("i", Call("Fin", n), All("h", Lt(Add(Val(i), D(1)), n),
            All("j", Fin(3), And(Bond(Cell(i, left), Cell(next, right)),
                Bond(Cell(i, right), Cell(next, left))))));
        Formula Earlier(byte colour) => Ex("q", cells,
            And(Lt(Rank(q), Rank(p)), Eq(App(a, q), D(colour))));
        var normal = All("p", cells, And(
            Imp(Or(Eq(App(a, p), D(2)), Or(Eq(App(a, p), D(3)), Eq(App(a, p), D(4)))), Earlier(1)),
            Imp(Eq(App(a, p), D(3)), Earlier(2))));
        var predicate = Seq(LambdaLower, Sp, a, Colon, Sp, Arrow(cells, Fin(6)), Sp,
            Mapsto, Sp, Par(And(first, And(horizontal, And(diagonal, normal)))));
        return All("n", V("Nat"), Eq(Call("a", n),
            Call("Finset.card", Call("Finset.filter", predicate, Call("Finset.univ")))));
    }

    private static Formula ResultFormula()
    {
        var x = V("X"); var n = V("n");
        var series = Call("PowerSeries.mk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp,
            Mapsto, Sp, Par(Seq(Call("a", n), Colon, Sp, V("Rat")))));
        var numerator = Mul(Mul(D(2), x), Add(Sub(D(5), Mul(D(2,4,0), x)), Mul(D(2,0,4,8), Pow(x, D(2)))));
        var denominator = Mul(Sub(D(1), Mul(D(1,6), x)),
            Add(Sub(D(1), Mul(D(1,1,2), x)), Mul(D(1,0,2,4), Pow(x, D(2)))));
        return Seq(Eq(series, Mul(numerator, Pow(Par(denominator), new Formula.Negate(Num(1))))),
            Sp, Name("in"), Sp, Call("PowerSeries", V("Rat")));
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
