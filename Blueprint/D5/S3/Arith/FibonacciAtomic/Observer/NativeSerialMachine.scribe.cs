using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSerialMachineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialMachine.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSerialMachine", H("NativeSerialMachine"), Blocks(
            Entry("Op", "Source-free local instructions", "The transition function receives only control. Control may be infinite and may contain unbounded local workspace and all common retained inputs. Read returns exactly one four-valued physical reply. ApplyRho has no source-dependent return value. Stop returns the complete output.", DescribeRole.Definition),
            Entry("Event", "Chronological physical actions", "Every local step and real update is recorded. Every Read invocation contributes one event, including repeated addresses. Epoch and address are literal descriptors of the physical call.", DescribeRole.Definition),
            Entry("reads", "Chronological literal Read events", "Filtering removes only local and update markers. It preserves chronological order and multiplicity. The length of this list is the raw-call cost.", DescribeRole.Definition),
            Entry("answers", "Reply words and raw cost", "The reply word maps the chronological Read event list to its four-valued replies. Its length equals the number of Read invocations; local actions and updates contribute zero raw calls. In the formulas ReadEvent is Event.read, tuple is the displayed product constructor, iterate is Function.iterate, result is the final Sum component of Boundary, append is chronological list append, and IsPrefix is the list prefix relation.", DescribeRole.Definition),
            Entry("Config", "Actual physical configuration", "A configuration consists of source-free local control, certified epoch, one actual native source register and the complete retained action trace. Neither the register nor that trace is an argument of the local transition function.", DescribeRole.Definition),
            Entry("Boundary", "Next observable boundary", "A boundary records the exact control and actual epoch together with either the next physical address or the entire terminal output.", DescribeRole.Definition),
            Entry("nativeStep", "One actual register step", "There is one physical source register. A local step changes control; Read inspects only its submitted address; ApplyRho substitutes the actual current tree and increments the certified epoch. The interpreter cannot inspect register size, shape, equality or timing.", DescribeRole.Definition),
            Entry("Run", "Finite actual termination", "The inductive rules retain every ordinary step, every true substitution update and every actual literal Read. Termination is sourcewise and supplies no uniform runtime or address bound.", DescribeRole.Definition),
            Entry("Replay", "Partial reply-word replay", "Replay receives only a finite reply word. It follows the same local and update steps and stops when that word has been consumed at the next Read or Stop. Unreachable words may have no finite replay.", DescribeRole.Definition),
            Entry("replay_deterministic", "Witness-independent replay", "A reply word has at most one finite replay trace and boundary. Equality includes the control, epoch, next physical address or complete terminal output.", DescribeRole.Theorem),
            Entry("operational_replay", "Actual runs supply replay boundaries", "An actual terminating run supplies a full terminal replay and a finite replay boundary before each actual Read. Every such word is shorter than the terminal reply list. Replay uniqueness makes the descriptors independent of the source used to establish existence.", DescribeRole.Theorem),
            Entry("reached_prefix_replay", "Every reached prefix reaches its next boundary", "Every prefix of a terminating run’s reply word has a finite source-free replay. Its full action trace is a prefix of the actual trace and has exactly the supplied replies. Its boundary is Stop with the actual output exactly when the whole reply word has been consumed. This is an existence result from an actual terminating source, not an effective stopping oracle.", DescribeRole.Theorem),
            Entry("actual_register_execution", "Certified physical evolution", "Starting from the actual iterated original source at the certified epoch, execution reaches the actual iterated source at its final epoch, which is at least the initial epoch. Appending the full chronological trace to any retained prior trace is exact. Every Read is truthful at its actual epoch.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeserialmachine-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement(name))) : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string name) => name switch
    {
        "replay_deterministic" => EpochProgram(All("w",Call("List",V("Reply")),All("t,s",V("Trace"),All("b,d",Call("Boundary",V("C"),V("O")),Imp(Rep("w","t","b"),Imp(Rep("w","s","d"),And(EqOf(V("t"),V("s")),EqOf(V("b"),V("d"))))))))),
        "operational_replay" => EpochProgram(All("r",V("Source"),All("t",V("Trace"),All("o",V("O"),Imp(Call("Run",V("delta"),V("c"),V("e"),V("r"),V("t"),V("o")),And(
 Some("next",V("C"),Some("epoch",V("Nat"),Call("Replay",V("delta"),V("c"),V("e"),Ans("t"),V("t"),Tup(V("next"),V("epoch"),Call("inr",V("o")))))),
 All("n",V("Nat"),All("a",V("Address"),All("y",V("Reply"),Imp(Mem(Call("ReadEvent",V("n"),V("a"),V("y")),V("t")),Some("w",Call("List",V("Reply")),Some("s",V("Trace"),Some("next",V("C"),And(Lt(Len(V("w")),Len(Ans("t"))),Call("Replay",V("delta"),V("c"),V("e"),V("w"),V("s"),Tup(V("next"),V("n"),Call("inl",V("a")))))))))))),
 All("w",Call("List",V("Reply")),All("s,z",V("Trace"),All("b,d",Call("Boundary",V("C"),V("O")),Imp(Rep("w","s","b"),Imp(Rep("w","z","d"),And(EqOf(V("s"),V("z")),EqOf(V("b"),V("d"))))))))
 )))))),
        "reached_prefix_replay" => EpochProgram(All("r",V("Source"),All("t",V("Trace"),All("o",V("O"),Imp(Call("Run",V("delta"),V("c"),V("e"),V("r"),V("t"),V("o")),All("w",Call("List",V("Reply")),Imp(PrefixOf(V("w"),Ans("t")),Some("s",V("Trace"),Some("b",Call("Boundary",V("C"),V("O")),And(Rep("w","s","b"),PrefixOf(V("s"),V("t")),EqOf(Ans("s"),V("w")),IffOf(EqOf(V("w"),Ans("t")),EqOf(Call("result",V("b")),Call("inr",V("o")))))))))))))),
        "actual_register_execution" => EpochProgram(All("r",V("Source"),All("t",V("Trace"),All("o",V("O"),Imp(Call("Run",V("delta"),V("c"),V("e"),V("r"),V("t"),V("o")),All("u",V("Source"),Imp(EqOf(V("r"),Root("e","u")),All("old",V("Trace"),Some("next",V("C"),Some("epoch",V("Nat"),And(Le(V("e"),V("epoch")),Call("Reaches",Call("nativeStep",V("delta")),Tup(V("c"),V("e"),V("r"),V("old")),Tup(V("next"),V("epoch"),Root("epoch","u"),Call("append",V("old"),V("t")))),EqOf(Call("delta",V("next")),Call("stop",V("o"))),All("n",V("Nat"),All("a",V("Address"),All("y",V("Reply"),Imp(Mem(Call("ReadEvent",V("n"),V("a"),V("y")),V("t")),EqOf(Call("readout",V("a"),Root("n","u")),V("y"))))))))))))))))),
        _ => throw new ArgumentException(name)
    };

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Ans(string t) => Call("answers", V(t));
    private static Formula Len(Formula t) => Call("length", t);
    private static Formula Root(string e, string u) => Call("iterate", V("substitution"), V(e), V(u));
    private static Formula Tup(params Formula[] args) => Call("tuple", args);
    private static Formula Rep(string w, string t, string b) => Call("Replay", V("delta"), V("c"), V("e"), V(w), V(t), V(b));
    private static Formula Program(Formula body) => All("C,O", V("Type"), All("delta", Arr(V("C"),Call("Op",V("C"),V("O"))), All("c",V("C"),body)));
    private static Formula EpochProgram(Formula body) => Program(All("e",V("Nat"),body));
    private static Formula PrefixOf(Formula a, Formula b) => Call("IsPrefix",a,b);
}
