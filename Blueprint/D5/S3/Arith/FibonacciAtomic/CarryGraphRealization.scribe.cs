using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class CarryGraphRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/CarryGraphRealization.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Par(Seq(Forall, Sp, x, Colon, Sp, type, Comma, Sp, body));
    private static Formula And(params Formula[] fs) => Par(Seq(fs.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray()));
    private static Formula Imp(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var g = V("gamma"); var d = V("d"); var i = V("i");
        var tape = V("tape"); var words = V("words");
        var n = Seq(Mathbb, Grp(V("N")));
        var path = V("Path"); var bits = Call("List", V("Bool"));
        Formula PD(Formula f) => All(m, n, All(g, path, All(d, n, f)));
        Formula PT(Formula f) => All(m, n, All(g, path, All(tape, V("Tape"), f)));
        Formula PI(Formula f) => All(m, n, All(g, path, All(i, Call("Fin", m), f)));
        var r = Call("r", Call("state", g, d));
        var e = Call("e", Call("state", g, d));
        var b = Call("b", Call("action", g, d));
        var h = Call("h", Call("action", g, d));
        var c = Call("c", Call("action", g, d));
        var upper = Seq(e, Sp, Plus, Sp, c);
        var selected = Par(Seq(
            Par(Seq(Equal(b, D(1)), Sp, Land, Sp, i, Sp, Lt, Sp, upper)),
            Sp, Lor, Sp,
            Par(Seq(b, Sp, Neq, Sp, D(1), Sp, Land, Sp,
                Seq(e, Sp, Minus, Sp, h), Sp, Le, Sp, i, Sp, Land, Sp, i, Sp, Lt, Sp, upper))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Fixed one-label intervals determine ordered children and an actual bit-by-bit scan.",
            H("Fixed-label Carry-tree Execution"), Blocks(
                Def("labelSet", "Fixed labels", PD(All(i, Call("Fin", m),
                    Seq(i, Sp, InMacro, Sp, Call("labelSet", m, g, d), Sp, Iff, Sp, selected))),
                    "Indices are zero-based. On an anchor-one column the selected labels start at zero. On an anchor-zero column they start at e-h and stop before e+c."),
                Def("labelDigit", "Output digits",
                    PI(All(d, n, Equal(Call("labelDigit", g, i, d), Call("indicator", Call("labelSet", m, g, d), i)))) ,
                    "Membership in the selected set gives digit one; every other label has digit zero."),
                Def("scan", "Charged scan",
                    PT(All(d, n, Seq(Call("scan", m, g, tape, d), Sp, InMacro, Sp,
                        Call("Sum", Call("Product", Call("Fin", m), n), n)))),
                    "The root is active slot zero. At depth d an active slot j reads tape(d), forms z=2j+toNat(tape(d)), and returns the z-th column label with charge d+1 if z is below the label count. Otherwise it continues in slot z minus that count. A returned state stays unchanged and reads no further bits."),
                Def("children", "Ordered children",
                    All(words, Call("List", bits), Equal(Call("children", words), Call("flatMap", Par(Seq(V("w"), Sp, Mapsto, Sp, Seq(OpenBracket, Call("append", V("w"), Seq(OpenBracket, V("false"), CloseBracket)),
                        Comma, Sp, Call("append", V("w"), Seq(OpenBracket, V("true"), CloseBracket)), CloseBracket))), words))),
                    "Each word contributes first its false child and then its true child, preserving parent order."),
                Def("continuing", "Continuing words",
                    PD(Equal(Call("continuing", m, g, Seq(d, Sp, Plus, Sp, D(1))),
                        Call("drop", Call("length", Call("sort", Call("labelSet", m, g, d))),
                            Call("children", Call("continuing", m, g, d))))),
                    "Depth zero consists of the empty word. Every later level expands the continuing parents and removes the initial children assigned to labels."),
                Def("stopping", "Labelled stopping words",
                    PD(Equal(Call("stopping", m, g, d),
                        Call("zip", Call("children", Call("continuing", m, g, d)),
                            Call("sort", Call("labelSet", m, g, d))))),
                    "The selected initial children are paired with the increasing output labels. The zip has the shorter of the two input lengths."),
                Def("sample", "First return",
                    PT(Equal(Call("sample", m, g, tape), Call("firstLeft", Call("scan", m, g, tape)))),
                    "The sample is the first left scan state, with its output label and charged length. It is absent on tapes with no finite return."),
                Def("bill", "Total charged reads",
                    PT(Equal(Call("bill", m, g, tape),
                        Seq(new Formula.Subscript(F.Sum, Seq(d, Sp, InMacro, Sp, n)),
                            Call("indicator", V("isRight"), Call("scan", m, g, tape, d))))),
                    "The nonnegative extended-real sum counts one read for each active scan state. It is infinite on an execution that remains active forever."),
                Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                    H("Every root path has its actual fair-bit tree"),
                    StatementSource.FromAuthor(Disp(ResultFormula())), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("For every m at least two and every legal root path, the fixed digits give a nonnegative normalized law. Index zero is the minimum anchor and equals its digit series; a positive anchor makes every label positive.")),
                        Paragraph(Text("The constructed stopping words are prefix-free and carry exactly the selected labels at each depth. The first-return sample outputs a label and length exactly when its tape prefix is that labelled leaf. Its bill is that length, so each consumed fair bit is charged once. Under the existing independent fair-tape measure its label law is the digit law, its stopping tail is r(d)/2^d, and it returns almost surely. The expected bill equals pathCost, is at most m, and dominates the existing dyadic cost. No canonical-expansion, rationality or computability hypothesis is added."))),
                    DescribeRole.Theorem))));
    }
    private static Formula ResultFormula()
    {
        var m = V("m"); var g = V("gamma"); var i = V("i"); var d = V("d");
        var t = V("tape"); var k = V("n"); var w = V("w");
        var n = Seq(Mathbb, Grp(V("N"))); var indices = Call("Fin", m);
        Formula P(Formula x) => Call("ofDigits", Call("labelDigit", g, x));
        Formula A(Formula x) => Seq(D(0), Sp, Le, Sp, x);
        Formula Pos(Formula x) => Seq(D(0), Sp, Lt, Sp, x);
        Formula Ex(Formula x, Formula ty, Formula f) => Par(Seq(Exists, Sp, x, Colon, Sp, ty, Comma, Sp, f));
        Formula Pair(Formula x, Formula y) => Par(Seq(x, Comma, Sp, y));
        Formula Event(Formula f) => Seq(OpenBrace, t, Sp, InMacro, Sp, V("Tape"), Mid, f, CloseBrace);
        Formula Returned(Formula depth) => Equal(Call("sample", m, g, t), Call("some", Pair(i, depth)));
        var anchor = Call("anchorValue", g); var sample = Call("sample", m, g, t);
        var cost = Call("pathCost", g); var next = Seq(d, Sp, Plus, Sp, D(1));
        var leaves = Call("stopping", m, g, d);
        var tail = Event(Par(Seq(Equal(sample, V("none")), Sp, Lor, Sp,
            Ex(i, indices, Ex(k, n, And(Returned(k), Seq(d, Sp, Lt, Sp, k)))))));
        var returned = Event(Ex(k, n, Returned(k)));
        var leafSet = Seq(OpenBrace, w, Sp, InMacro, Sp, Call("List", V("Bool")), Mid,
            Ex(d, n, Ex(i, indices, Seq(Pair(w, i), Sp, InMacro, Sp, leaves))), CloseBrace);
        var clauses = And(All(i, indices, A(P(i))),
            Equal(Seq(new Formula.Subscript(F.Sum, Seq(i, Sp, InMacro, Sp, indices)), P(i)), D(1)),
            Equal(P(D(0)), anchor), All(i, indices, Seq(anchor, Sp, Le, Sp, P(i))),
            Imp(Pos(anchor), All(i, indices, Pos(P(i)))), Call("IsPrefixFree", leafSet),
            All(d, n, And(Equal(Call("map", V("snd"), leaves), Call("sort", Call("labelSet", m, g, d))),
                All(w, Call("Product", Call("List", V("Bool")), indices),
                    Imp(Seq(w, Sp, InMacro, Sp, leaves), Equal(Call("length", Call("fst", w)), next))))),
            All(t, V("Tape"), All(i, indices, All(d, n, Seq(Returned(next), Sp, Iff, Sp,
                Pair(Call("prefix", t, next), i), Sp, InMacro, Sp, leaves)))),
            All(t, V("Tape"), All(i, indices, All(k, n,
                Imp(Returned(k), Equal(Call("bill", m, g, t), k))))),
            All(i, indices, And(Call("MeasurableSet", returned),
                Equal(Call("fairTape", returned), Call("ofReal", P(i))))),
            All(d, n, And(Call("MeasurableSet", tail), Equal(Call("fairTape", tail),
                Call("ofReal", new Formula.Fraction(Call("r", Call("state", g, d)),
                    new Formula.Power(D(2), d)))))),
            Par(Seq(new Formula.Power(Forall, Call("ae", V("fairTape"))), Sp,
                t, Colon, Sp, V("Tape"), Comma, Sp, Ex(i, indices, Ex(k, n, Returned(k))))),
            Equal(Call("lintegral", V("fairTape"), Call("bill", m, g)), Call("ofReal", cost)),
            Seq(cost, Sp, Le, Sp, m), Seq(Call("cost", Par(Seq(i, Colon, Sp, indices, Sp, Mapsto, Sp, P(i)))), Sp, Le, Sp, cost));
        return All(m, n, Imp(Seq(D(2), Sp, Le, Sp, m), All(g, V("Path"),
            Imp(Call("IsRootPath", m, g), clauses))));
    }
}
