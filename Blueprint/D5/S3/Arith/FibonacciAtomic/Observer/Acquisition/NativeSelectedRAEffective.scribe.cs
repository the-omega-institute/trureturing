using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition;

internal sealed class NativeSelectedRAEffectiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAEffective.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A single effective source independent machine with complete selected rows.",
        H("Effective native selected production"), Blocks(
            Paragraph(Text("The complete configuration consists of entry, active finite control with unbounded finite address and byte regions, or the common ready configuration. "
                + "The program takes no source, schedule, update count or size bound as input. Its only source access is the actual Read reply.")),
            Def("encodeState", "The whole finite configuration code",
                "An injective natural code retains every field of Work and both selected ready rows. Work is encoded as its finite control, two finite binary addresses, finite sixteen letter row and three finite reply latches. "
                + "The state constructors use disjoint sum codes. This is a code of all accessible cells; no workspace field is projected away."),
            Def("finiteInstruction", "Finite data for each microstep",
                "Each Read instruction carries its address and all four encoded continuation configurations. Every local instruction carries its whole encoded successor. Ready is a separate Return. "
                + "The finite program counter is dispatched independently of the unbounded data regions. List append, retraction, last cell tests and constructor tests are primitive recursive."),
            Def("numericInstruction", "The total numeric instruction function",
                "Decode the complete natural control and execute finiteInstruction. Invalid natural codes use the same fixed entry configuration. This total function is primitive recursive."),
            Def("encodedOp", "Exact instruction correspondence",
                "Encode just the complete control of a local step or each of the four Read continuations, preserving the actual address and instruction kind. Return stays Return."),
            Describe.Lean(DescribeId.Create("native-selected-ra-effective-machine"),
                DeclarationHandle.Create(Prefix + "effective_selected_machine"),
                H("One recursive program realizes every microstep"), StatementSource.FromAuthor(Disp(Effective())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "There is one finite recursive code computing numericInstruction at every natural control, and its transition at every encoded actual configuration is exactly encodedOp of the original step. "
                    + "The primitive recursive construction covers all controls and data lengths, including configurations not reachable from entry. It identifies one actual program instruction at a time, preserving local steps and the separate Return. "
                    + "It makes no claim that the evaluator's own internal computation steps are physical observer instructions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-selected-ra-producer-contract"),
                DeclarationHandle.Create(Prefix + "selected_producer_contract"),
                H("Complete source independent selected production"), StatementSource.FromAuthor(Contract()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The single native selected machine has the effective complete control implementation above. Every legal finite returning history has its actual successful validation Read, and its whole retained row decodes to the literal record of its actual selected cut on that same validation source. "
                    + "Only local observer instructions, independent writer updates and the separate Return follow validation. Every finite source returns under every schedule with finitely many active writer updates. "
                    + "The continuation starts from the actual interrupted state after the final update, retaining its cursor and saved replies. "
                    + "The entire ready root row has invocation source support exactly the singleton alpha. The root literal record itself is compatible with every source and every substitution iterate, so the selected cut retains the distinction. "
                    + "Ready retains the selected cut and whole row and has no Work constructor or stored execution archive. These are finite cell and accessible state statements; physical allocator erasure is not asserted."))),
                DescribeRole.Theorem))));
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-selected-ra-effective-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string n) => F.Id(n);
    private static Formula Op(string n) => Seq(Operatorname, Grp(V(n)));
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Op(n), [.. a]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string n, Formula type, Formula body) =>
        Seq(Exists, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula AndOf(params Formula[] a) => Join(a, Land);
    private static Formula Join(Formula[] a, Formula relation)
    {
        Formula result = Par(a[0]);
        for (int i = 1; i < a.Length; ++i) result = Seq(result, Sp, relation, Sp, Par(a[i]));
        return result;
    }
    private static Formula World(string index) => Call("trajectory", V("s"),
        Call("world", Op("entry"), V("u"), Op("false")), V(index));
    private static Formula Effective() => AndOf(Call("Injective", Op("encodeState")),
        Some("P", Op("EffectiveProgram"), All("x", Op("State"),
            Equal(Call("transition", V("P"), Call("encodeState", V("x"))),
                Call("encodedOp", Call("step", V("x")))))));
    private static Formula Contract()
    {
        Formula sound = All("u", Op("Source"), All("h", Op("Word"), All("b", Op("State"),
            Seq(Call("Run", Op("step"), Op("entry"), V("u"), V("h"), V("b")), Sp, Implies, Sp,
                Some("q", Op("Bool"), Some("r", Call("List", Op("Cell")), AndOf(
                    Equal(V("b"), Call("ready", V("q"), V("r"))),
                    Call("Captured", V("u"), Call("eventSchedule", V("h")),
                        Call("length", V("h")), V("q"), V("r")))))))));
        Formula pending = AndOf(Equal(Call("apply", V("s"), V("n")), Op("true")),
            Equal(Call("returned", World("n")), Op("false")));
        Formula events = Seq(OpenBrace, V("n"), Colon, Op("Nat"), Sp, Vert, Sp, pending, CloseBrace);
        Formula live = All("u", Op("Source"), All("s", Seq(Op("Nat"), Sp, To, Sp, Op("Bool")),
            Seq(Call("Finite", events), Sp, Implies, Sp,
                Some("m", Op("Nat"), Equal(Call("returned", World("m")), Op("true"))))));
        Formula support = All("u", Op("Source"), Seq(
            Some("h", Op("Word"), Call("Run", Op("step"), Op("entry"), V("u"), V("h"),
                Call("ready", Op("true"), Op("rootBytes")))), Sp, Iff, Sp, Equal(V("u"), Call("of", Op("true")))));
        Formula compatible = All("u", Op("Source"), All("j", Op("Nat"), Equal(
            Call("literalRecord", Seq(OpenBrace, Op("emptyAddress"), CloseBrace),
                Call("iterate", Op("substitution"), V("j"), V("u"))), Op("rootLabel"))));
        return Disp(AndOf(Effective(), sound, live, support, compatible));
    }
}
