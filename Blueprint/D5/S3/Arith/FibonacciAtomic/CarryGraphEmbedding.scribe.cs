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
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body));
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
            "Bounded carry states and fixed label intervals determine exact continuing and stopping tree layers.",
            H("Original Carry Graph and Fixed Tree Layers"),
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
                Def("labelSet", "Fixed labels", FixedLabelFormula(),
                    "Indices are zero-based. On an anchor-one column the selected labels start at zero. On an anchor-zero column they start at e-h and stop before e+c."),
                Def("children", "Ordered children", ChildrenFormula(),
                    "Each word contributes first its false child and then its true child, preserving parent order."),
                Def("continuing", "Continuing words", All(m, N, All(g, V("Path"), All(d, N,
                    Equal(Call("continuing", m, g, Add(d, D(1))),
                        Call("drop", Call("length", Call("sort", Call("labelSet", m, g, d))),
                            Call("children", Call("continuing", m, g, d))))))),
                    "Depth zero consists of the empty word. Every later level expands the continuing parents and removes the initial children assigned to labels."),
                Def("stopping", "Labelled stopping words", All(m, N, All(g, V("Path"), All(d, N,
                    Equal(Call("stopping", m, g, d),
                        Call("zip", Call("children", Call("continuing", m, g, d)),
                            Call("sort", Call("labelSet", m, g, d))))))),
                    "The selected initial children are paired with the increasing output labels. The zip has the shorter of the two input lengths."),
                Describe.Lean(DescribeId.Create("tree-layers"), DeclarationHandle.Create(Prefix + "tree_layers"),
                    H("Exact continuing and stopping layers"), StatementSource.FromAuthor(Disp(TreeFormula())),
                    AssessedProvenance.FromRepo(), Blocks(
                        Paragraph(Text("For every natural m and legal root path, the number of selected labels is the column's one-label count. At depth d the continuing list has exactly r(d) distinct words, each of length d. The stopping list pairs distinct words of length d+1 with every selected label in increasing order.")),
                        Paragraph(Text("The label interval has e+c entries on an anchor-one column and h+c entries on an anchor-zero column. Doubling the continuing parents and removing that interval leaves exactly the successor residual width. Induction also preserves distinctness and word length. The scan and fair-bit law use these exact tree layers."))),
                    DescribeRole.Theorem))));
    }

    private static Formula FixedLabelFormula()
    {
        var m = V("m"); var g = V("gamma"); var d = V("d"); var i = V("i");
        var e = Call("e", Call("state", g, d));
        var b = Call("b", Call("action", g, d));
        var h = Call("h", Call("action", g, d));
        var c = Call("c", Call("action", g, d));
        var selected = Par(Seq(
            And(Equal(b, D(1)), Seq(i, Sp, Lt, Sp, Add(e, c))), Sp, Lor, Sp,
            And(Seq(b, Sp, Neq, Sp, D(1)), Leq(Sub(e, h), i), Seq(i, Sp, Lt, Sp, Add(e, c)))));
        return All(m, N, All(g, V("Path"), All(d, N, All(i, Call("Fin", m),
            Seq(i, Sp, InMacro, Sp, Call("labelSet", m, g, d), Sp, Iff, Sp, selected)))));
    }

    private static Formula ChildrenFormula()
    {
        var words = V("words"); var bits = Call("List", V("Bool"));
        return All(words, Call("List", bits), Equal(Call("children", words),
            Call("flatMap", Par(Seq(V("w"), Sp, Mapsto, Sp,
                Seq(OpenBracket, Call("append", V("w"), Seq(OpenBracket, V("false"), CloseBracket)),
                    Comma, Sp, Call("append", V("w"), Seq(OpenBracket, V("true"), CloseBracket)), CloseBracket))), words)));
    }

    private static Formula TreeFormula()
    {
        var m = V("m"); var g = V("gamma"); var d = V("d"); var w = V("w");
        var indices = Call("Fin", m); var bits = Call("List", V("Bool"));
        var labels = Call("sort", Call("labelSet", m, g, d));
        var active = Call("continuing", m, g, d); var leaves = Call("stopping", m, g, d);
        var state = Call("state", g, d); var action = Call("action", g, d);
        return All(m, N, All(g, V("Path"), Imp(Call("IsRootPath", m, g), And(
            All(d, N, Equal(Call("length", labels), Call("ones", state, action))),
            All(d, N, And(Equal(Call("length", active), Call("r", state)), Call("Nodup", active),
                All(w, bits, Imp(Seq(w, Sp, InMacro, Sp, active), Equal(Call("length", w), d))))),
            All(d, N, And(Equal(Call("map", V("snd"), leaves), labels), Call("Nodup", leaves),
                All(w, Call("Product", bits, indices), Imp(Seq(w, Sp, InMacro, Sp, leaves),
                    Equal(Call("length", Call("fst", w)), Add(d, D(1)))))))))));
    }
}
