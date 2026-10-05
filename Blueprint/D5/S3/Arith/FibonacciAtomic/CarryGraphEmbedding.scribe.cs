using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CarryGraphEmbeddingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CarryGraphEmbedding.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Z => Seq(Mathbb, Grp(V("Z")));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula Ex(Formula x, Formula type, Formula body) =>
        Par(Seq(Exists, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula And(params Formula[] parts) =>
        Par(Seq(parts.SelectMany((f, i) => i == 0
            ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, Rightarrow, Sp, b));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Pow(Formula d) => new Formula.Power(D(2), d);
    private static Formula Sum(Formula i, Formula domain, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, domain)), body);
    private static Formula Tuple(params Formula[] fields) =>
        Par(Seq(fields.SelectMany((f, i) => i == 0
            ? new[] { f } : new[] { Comma, Sp, f }).ToArray()));

    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var s = V("s"); var a = V("a"); var d = V("d");
        var r = Call("r", s); var e = Call("e", s);
        var b = Call("b", a); var h = Call("h", a); var c = Call("c", a);
        var g = V("gamma"); var state = Call("state", g, d); var action = Call("action", g, d);
        var succ = Call("successor", s, a);
        var rowOne = And(Equal(b, D(1)), Equal(h, D(0)), Leq(D(0), c), Leq(c, Sub(m, e)));
        var rowZero = And(Equal(b, D(0)), Leq(D(0), h), Leq(h, Sub(e, D(1))),
            Leq(D(0), c), Leq(c, Sub(m, e)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive real laws enter the original bounded carry graph with exact minimum-anchor and tail-cost values.",
            H("Canonical Embedding in the Original Carry Graph"),
            Blocks(
                Def("State", "State coordinates", Equal(V("State"), Tuple(Z, Z)),
                    "A state has integer fields r and e. The graph bounds are imposed by IsState; raw coordinate pairs need not obey them."),
                Def("Action", "Column parameters", Equal(V("Action"), Tuple(Z, Z, Z)),
                    "An action has integer fields b, h and c, in that order. Its bit is b, h counts departures from the anchor equality group, and c counts larger-prefix labels taking a one."),
                Def("IsState", "Bounded graph states", All(m, N, All(s, V("State"),
                    Seq(Call("IsState", m, s), Sp, Iff, Sp,
                        And(Leq(D(0), r), Leq(r, Sub(m, D(1))), Leq(D(1), e), Leq(e, m))))),
                    "Every integer pair with residual width between zero and m-1 and equality-group size between one and m belongs to the graph."),
                Def("root", "Root", All(m, N, Equal(Call("root", m), Tuple(D(1), m))),
                    "For m at least two the root is a graph state: one continuing cylinder and all m labels equal at depth zero."),
                Def("ones", "One-label count", All(s, V("State"), All(a, V("Action"),
                    And(Imp(Equal(b, D(1)), Equal(Call("ones", s, a), Add(e, c))),
                        Imp(Seq(b, Sp, Neq, Sp, D(1)), Equal(Call("ones", s, a), Add(h, c)))))),
                    "The one-bit row emits e+c one-labels. Every other raw bit value uses h+c; legal actions restrict the bit to zero or one."),
                Def("successor", "Successor", All(s, V("State"), All(a, V("Action"),
                    Equal(succ, Tuple(Sub(Mul(D(2), r), Call("ones", s, a)), Sub(e, h))))),
                    "The successor subtracts the column's one-label count from twice the residual and removes h labels from the equality group."),
                Def("Legal", "Two legal action rows", All(m, N, All(s, V("State"), All(a, V("Action"),
                    Seq(Call("Legal", m, s, a), Sp, Iff, Sp,
                        And(Call("IsState", m, s), Par(Seq(rowOne, Sp, Lor, Sp, rowZero)),
                            Call("IsState", m, succ)))))),
                    "A legal action satisfies exactly one displayed bit row and has a bounded successor. The equality-group bounds on the successor also follow from the row's inequalities; writing them explicitly identifies both endpoints as graph states."),
                Def("Path", "Infinite columns", Equal(V("Path"),
                    Tuple(Seq(N, Sp, To, Sp, V("State")), Seq(N, Sp, To, Sp, V("Action")))),
                    "A path carries two sequences, state and action. Index d names the state at depth d and the action producing the next bit at depth d+1."),
                Def("IsRootPath", "Legal root paths", All(m, N, All(g, V("Path"),
                    Seq(Call("IsRootPath", m, g), Sp, Iff, Sp,
                        And(Equal(Call("state", g, D(0)), Call("root", m)),
                            All(d, N, And(Call("Legal", m, state, action),
                                Equal(Call("state", g, Add(d, D(1))), Call("successor", state, action)))))))),
                    "Every column has a legal action and its recorded next state is that action's successor, starting from the root."),
                Def("anchorValue", "Anchor series", All(g, V("Path"), Equal(Call("anchorValue", g),
                    Sum(d, N, new Formula.Fraction(Call("b", action), Pow(Add(d, D(1))))))),
                    "The anchor value is the real infinite sum of column bits, with column zero weighted by one half. This convention includes terminating binary expansions. An unsummable real series on an arbitrary raw path has the totalized value zero."),
                Def("pathCost", "Residual tail cost", All(g, V("Path"), Equal(Call("pathCost", g),
                    Sum(d, N, new Formula.Fraction(Call("r", state), Pow(d))))),
                    "The cost is the real infinite sum of normalized residual widths, including the depth-zero term. These whole-column quantities do not charge r separate reads in a machine step. An unsummable series on a raw path has the totalized value zero."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Complete canonical embedding"), StatementSource.FromAuthor(Disp(ResultFormula())),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every m>=2, each graph state has a legal action. At residual zero the only legal action has b=h=c=0 and leaves the state fixed. At equality-group size one every legal action has h=0.")),
                        Paragraph(Text("Let p be any strictly positive real probability vector, and choose any index k minimizing p. Write n(i,d)=floor(2^d p(i)) and a(i,d)=n(i,d+1)-2n(i,d). The path has r(d)=R(p,d), e(d) equal to the number of indices with n(i,d)=n(k,d), and anchor bit a(k,d). Its anchor value is p(k), hence the smallest probability, and its tail cost is the existing dyadic cost L(p). No rationality, distinctness or computability hypothesis is used.")),
                        Paragraph(Text("Minimum-prefix monotonicity and the zero-or-one digit bounds show that a label with strictly larger old prefix has strictly larger next prefix. Equal-prefix labels taking a different bit therefore leave permanently. When the anchor bit is one, minimum-prefix order forces every equal-prefix label to take one. When it is zero, fewer than e equal-prefix labels depart because the anchor stays. Counting these departures and the larger-prefix one-labels gives exactly the two legal action rows. The floor remainder bounds supply the residual interval, and the canonical binary expansion reconstructs the minimum atom."))),
                    DescribeRole.Theorem))));
    }

    private static Formula ResultFormula()
    {
        var m = V("m"); var s = V("s"); var a = V("a"); var p = V("p");
        var k = V("k"); var i = V("i"); var d = V("d"); var g = V("gamma");
        var indices = Call("Fin", m); var state = Call("state", g, d);
        var action = Call("action", g, d);
        Formula PrefixAt(Formula index, Formula depth) =>
            new Formula.Floor(Mul(Pow(depth), Call("p", index)));
        var available = All(s, V("State"), Imp(Call("IsState", m, s),
            Ex(a, V("Action"), Call("Legal", m, s, a))));
        var absorbing = All(s, V("State"), All(a, V("Action"),
            Imp(Equal(Call("r", s), D(0)), Imp(Call("Legal", m, s, a),
                And(Equal(Call("b", a), D(0)), Equal(Call("h", a), D(0)),
                    Equal(Call("c", a), D(0)), Equal(Call("successor", s, a), s))))));
        var singleton = All(s, V("State"), All(a, V("Action"),
            Imp(Equal(Call("e", s), D(1)), Imp(Call("Legal", m, s, a), Equal(Call("h", a), D(0))))));
        var group = Call("card", Seq(OpenBrace, i, Sp, InMacro, Sp, indices, Mid,
            PrefixAt(i, d), Sp, Eq, Sp, PrefixAt(k, d), CloseBrace));
        var embedding = All(p, Seq(indices, Sp, To, Sp, Real),
            Imp(All(i, indices, Seq(D(0), Sp, Lt, Sp, Call("p", i))),
            Imp(Equal(Sum(i, indices, Call("p", i)), D(1)), All(k, indices,
            Imp(All(i, indices, Leq(Call("p", k), Call("p", i))), Ex(g, V("Path"),
                And(Call("IsRootPath", m, g),
                    All(d, N, Equal(Call("r", state), Call("R", p, d))),
                    All(d, N, Equal(Call("e", state), group)),
                    All(d, N, Equal(Call("b", action),
                        Sub(PrefixAt(k, Add(d, D(1))), Mul(D(2), PrefixAt(k, d))))),
                    Equal(Call("anchorValue", g), Call("p", k)),
                    Equal(Call("pathCost", g), Call("L", p)))))))));
        return All(m, N, Imp(Leq(D(2), m), And(available, absorbing, singleton, embedding)));
    }
}
