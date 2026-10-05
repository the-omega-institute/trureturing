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
                    "P(m) consists of all dependent tables assigning one legal action to each legal state. The map step(f) sends a state to the successor of its selected action. Its iterate defines the state sequence and the table gives the action sequence."))));
    }
}
