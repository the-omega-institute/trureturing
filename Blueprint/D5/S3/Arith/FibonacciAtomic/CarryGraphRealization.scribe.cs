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
    private static DocumentBlock Def(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create()
    {
        var m = V("m"); var g = V("gamma"); var d = V("d"); var i = V("i");
        var tape = V("tape"); var words = V("words");
        var n = Seq(Mathbb, Grp(V("N")));
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
                Def("labelSet", "Fixed labels", All(i, Call("Fin", m),
                    Seq(i, Sp, InMacro, Sp, Call("labelSet", m, g, d), Sp, Iff, Sp, selected)),
                    "Indices are zero-based. On an anchor-one column the selected labels start at zero. On an anchor-zero column they start at e-h and stop before e+c."),
                Def("labels", "Ordered column labels",
                    Equal(Call("labels", m, g, d), Call("sort", Call("labelSet", m, g, d))),
                    "The finite selected set is listed in increasing order. Each emitted child receives the label at the same position."),
                Def("labelDigit", "Output digits",
                    Equal(Call("labelDigit", g, i, d), Call("indicator", Call("labelSet", m, g, d), i)),
                    "Membership in the selected set gives digit one; every other label has digit zero."),
                Def("labelLaw", "Digit law",
                    Equal(Call("labelLaw", g, i), Call("ofDigits", Call("labelDigit", g, i))),
                    "The base-two real digit sum allows noncanonical tails of ones."),
                Def("scan", "Charged scan",
                    All(d, n, Seq(Call("scan", m, g, tape, d), Sp, InMacro, Sp,
                        Call("Sum", Call("Product", Call("Fin", m), n), n))),
                    "The root is active slot zero. At depth d an active slot j reads tape(d), forms z=2j+toNat(tape(d)), and returns the z-th column label with charge d+1 if z is below the label count. Otherwise it continues in slot z minus that count. A returned state stays unchanged and reads no further bits."),
                Def("children", "Ordered children",
                    Equal(Call("children", words), Call("flatMap", V("appendFalseThenTrue"), words)),
                    "Each word contributes first its false child and then its true child, preserving parent order."),
                Def("continuing", "Continuing words",
                    Equal(Call("continuing", m, g, Seq(d, Sp, Plus, Sp, D(1))),
                        Call("drop", Call("length", Call("labels", m, g, d)),
                            Call("children", Call("continuing", m, g, d)))),
                    "Depth zero consists of the empty word. Every later level expands the continuing parents and removes the initial children assigned to labels."),
                Def("stopping", "Labelled stopping words",
                    Equal(Call("stopping", m, g, d),
                        Call("zip", Call("children", Call("continuing", m, g, d)),
                            Call("labels", m, g, d))),
                    "The selected initial children are paired with the increasing output labels. The zip has the shorter of the two input lengths."),
                Def("sample", "First return",
                    Equal(Call("sample", m, g, tape), Call("firstLeft", Call("scan", m, g, tape))),
                    "The sample is the first left scan state, with its output label and charged length. It is absent on tapes with no finite return."),
                Def("bill", "Total charged reads",
                    Equal(Call("bill", m, g, tape),
                        Seq(new Formula.Subscript(F.Sum, Seq(d, Sp, InMacro, Sp, n)),
                            Call("indicator", V("isRight"), Call("scan", m, g, tape, d)))),
                    "The nonnegative extended-real sum counts one read for each active scan state. It is infinite on an execution that remains active forever."))));
    }
}
