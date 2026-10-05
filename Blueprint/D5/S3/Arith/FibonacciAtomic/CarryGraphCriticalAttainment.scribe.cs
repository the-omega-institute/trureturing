using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CarryGraphCriticalAttainmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CarryGraphCriticalAttainment.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Mul(Formula a, Formula b) => Par(Seq(a, Sp, Cdot, Sp, b));
    private static Formula Sub(Formula a, Formula b) => Par(Seq(a, Sp, Minus, Sp, b));
    private static Formula Add(Formula a, Formula b) => Par(Seq(a, Sp, Plus, Sp, b));
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pos(Formula a) => Seq(D(0), Sp, Lt, Sp, a);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Ty(string name) => Seq(Mathbb, Grp(V(name)));
    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var p = V("p"); var k = V("k"); var i = V("i"); var y = V("y");
        var x = V("x"); var v = V("v"); var s = V("s"); var a = V("a"); var f = V("f");
        var d = V("d"); var start = V("start");
        var states = Call("S", m); var actions = Call("A", m, s); var policies = Call("P", m);
        var lawType = Seq(Call("Fin", m), Sp, To, Sp, Ty("R"));
        var valueType = Seq(states, Sp, To, Sp, Ty("R"));
        var ratios = Seq(OpenBrace, y, Sp, InMacro, Sp, Ty("R"), Mid,
            Ex(p, lawType, Ex(k, Call("Fin", m), And(
                All(i, Call("Fin", m), Pos(Call("p", i))),
                Equal(Seq(new Formula.Subscript(F.Sum, i), Call("p", i)), D(1)),
                All(i, Call("Fin", m), Leq(Call("p", k), Call("p", i))),
                Equal(y, Frac(Call("cost", p), Call("p", k)))))), CloseBrace);
        var oneStep = Add(Call("r", s), Mul(Frac(D(1), D(2)),
            Call("inf", Seq(OpenBrace, Sub(Call("v", Call("successor", s, a)),
                Mul(x, Call("b", a))), Mid, a, Sp, InMacro, Sp, actions, CloseBrace))));
        var stateOrbit = Call("iterate", Call("step", f), d, start);
        return DocumentDefinition.Create(ScribeNode.Create(
            "The discounted root price detects the full real slope and yields a positive optimal output law.",
            H("Carry-graph Critical Attainment"), Blocks(
                Def("alpha", "Full real minimum-atom slope",
                    All(m, Ty("N"), Equal(Call("alpha", m), Call("inf", ratios))),
                    "The infimum ranges over every strictly positive real law of total mass one and every minimizing index. Ties do not change the ratio. The cost is the dyadic floor-tail cost."),
                Def("bellman", "Original-graph Bellman minimum",
                    All(m, Ty("N"), All(x, Ty("R"), All(v, valueType, All(s, states,
                        Equal(Call("bellman", m, x, v, s), oneStep))))),
                    "S(m) is the subtype of the original integer carry states satisfying IsState(m), and A(m,s) is the subtype of actions satisfying Legal(m,s). Every legal action is retained, including actions at unreachable states. The successor is the original carry successor. The price of the anchor bit carries the next-column discount."),
                Def("policyPath", "Stationary-table orbit",
                    All(m, Ty("N"), All(f, policies, All(start, states, All(d, Ty("N"), And(
                        Equal(Call("state", Call("policyPath", m, f, start), d), stateOrbit),
                        Equal(Call("action", Call("policyPath", m, f, start), d), Call("f", stateOrbit))))))),
                    "P(m) consists of all dependent tables assigning one legal action to each legal state. The map step(f) sends a state to the successor of its selected action. Its iterate defines the state sequence and the table gives the action sequence."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Root prices and critical attainment"), StatementSource.FromAuthor(Disp(ResultFormula())),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every m>=2 there are value functions and deterministic legal tables for all real prices. Each value is the unique finite Bellman fixed point on every state, and each table attains the one-step minimum at every state. The root is o=(1,m). The selected stationary root path attains the minimum over all legal root paths, not merely an infimum.")),
                        Paragraph(Text("The root is nonnegative exactly at prices at most alpha(m). At the critical price it is zero. The critical table has a positive anchor. Its fixed-label tree, given by labelDigit, sample and bill, returns a strictly positive normalized real law, with minimum mass equal to that anchor. It stops almost surely, has that return law under the independent fair bit tape, and its expected charged bill equals both the whole-column path cost and the dyadic cost. These costs equal alpha(m) times the anchor.")),
                        Paragraph(Text("Finite legal actions supply statewise minimum selectors. The half-discount fixed point comes from the finite Bellman contraction. Summing the one-step inequalities telescopes the discounted value sequence; bounded state values make the tail vanish. The inequalities are equalities along the selected table, so the root path attains the full path minimum.")),
                        Paragraph(Text("Canonical paths of positive real laws compare the root price with every cost-to-minimum-mass ratio. Arbitrarily close ratios to the infimum give root values smaller than epsilon/m at the critical price, so that value is zero without assuming attainment. The root path cost is at least one, which rules out a zero anchor. Its actual output law then gives alpha times the anchor at most the dyadic cost, at most the path cost, with both endpoints equal. This forces all costs to agree."))),
                    DescribeRole.Theorem))));
    }
    private static Formula ResultFormula()
    {
        var m = V("m"); var x = V("x"); var values = V("V"); var tables = V("f");
        var s = V("s"); var w = V("w"); var gamma = V("gamma"); var i = V("i");
        var tape = V("tape"); var n = V("n"); var root = V("o");
        var states = Call("S", m); var policies = Call("P", m); var indices = Call("Fin", m);
        var valueType = Seq(states, Sp, To, Sp, Ty("R")); var alpha = Call("alpha", m);
        Formula Value(Formula price, Formula state) => Call("V", price, state);
        Formula G(Formula price) => Call("policyPath", m, Call("f", price), root);
        Formula C(Formula path) => Call("pathCost", path);
        Formula T(Formula path) => Call("anchorValue", path);
        Formula Fixed(Formula price, Formula value) =>
            Equal(Call("bellman", m, price, value), value);
        Formula RootPrice(Formula price, Formula path) => Sub(C(path), Mul(price, T(path)));
        var action = Call("f", x, s);
        var selected = Add(Call("r", s), Mul(Frac(D(1), D(2)),
            Sub(Value(x, Call("successor", s, action)), Mul(x, Call("b", action)))));
        var unique = All(x, Ty("R"), And(Fixed(x, Call("V", x)),
            All(w, valueType, Imp(Fixed(x, w), Equal(w, Call("V", x))))));
        var greedy = All(x, Ty("R"), All(s, states, Equal(Value(x, s), selected)));
        var pathMinimum = All(x, Ty("R"), And(Call("IsRootPath", m, G(x)),
            Equal(Value(x, root), RootPrice(x, G(x))),
            All(gamma, V("Path"), Imp(Call("IsRootPath", m, gamma),
                Leq(Value(x, root), RootPrice(x, gamma))))));
        var sign = All(x, Ty("R"), Par(Seq(Leq(D(0), Value(x, root)), Sp, Iff, Sp, Leq(x, alpha))));
        var star = G(alpha);
        Formula Pstar(Formula index) => Call("ofDigits", Call("labelDigit", star, index));
        var law = Par(Seq(i, Colon, Sp, indices, Sp, Mapsto, Sp, Pstar(i)));
        var minimum = Call("inf", Seq(OpenBrace, Pstar(i), Mid, i, Sp, InMacro, Sp, indices, CloseBrace));
        var fair = V("fairTape");
        var returned = Equal(Call("sample", m, star, tape), Call("some", Par(Seq(i, Comma, Sp, n))));
        var eventSet = Seq(OpenBrace, tape, Sp, InMacro, Sp, V("Tape"), Mid, Ex(n, Ty("N"), returned), CloseBrace);
        var critical = And(Pos(T(star)), All(i, indices, Pos(Pstar(i))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), Pstar(i)), D(1)),
            Equal(minimum, T(star)),
            Par(Seq(new Formula.Power(Forall, Call("ae", fair)), Sp, tape, Colon, Sp, V("Tape"), Comma, Sp,
                Ex(i, indices, Ex(n, Ty("N"), returned)))),
            All(i, indices, Equal(Call("fairTape", eventSet), Call("ofReal", Pstar(i)))),
            Equal(Call("lintegral", fair, Call("bill", m, star)), Call("ofReal", C(star))),
            Equal(C(star), Call("cost", law)), Equal(Call("cost", law), Mul(alpha, T(star))));
        return All(m, Ty("N"), Imp(Leq(D(2), m),
            Ex(values, Seq(Ty("R"), Sp, To, Sp, valueType),
            Ex(tables, Seq(Ty("R"), Sp, To, Sp, policies),
                And(unique, greedy, pathMinimum, sign, Equal(Value(alpha, root), D(0)), critical)))));
    }

}
