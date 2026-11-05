using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Acquisition;

internal sealed class ContinuousAcquisitionTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous source-blind acquisition has an exact operational transport to terminal reset histories.",
        H("Preserving a continuous competitor's acquired information"),
        Blocks(
            Describe.Lean(DescribeId.Create("continuous-transport"),
                DeclarationHandle.Create(Prefix + "continuous_transport"),
                H("One public selector preserves every terminating run"),
                StatementSource.FromAuthor(TransportStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A controller has an arbitrary configuration space S, an initial configuration, "
                        + "a default output and one source-independent instruction function. The type "
                        + "binders S and L range over arbitrary, independently chosen universes. An instruction "
                        + "takes a local step, completes one original action with its fixed acknowledgement, "
                        + "requests a paid gcd reply, or halts with an output. A read continuation receives "
                        + "the complete natural-number reply. Source coordinates never enter the instruction "
                        + "function. True denotes R(a,b)=(b,a+b), and false denotes G(a,b)=(a+1,b). "
                        + "Only a paid read returns gcd(2a+3b,H).")),
                    Paragraph(Text(
                        "S need not be finite or bounded. A configuration can contain a finite program's "
                        + "instruction pointer, arbitrary finite binary working memory, retained records, "
                        + "public parameters and opaque handles. The semantic theorem even allows arbitrary "
                        + "transition functions, a larger class than effective finite programs. Every finite "
                        + "source-blind program with the stated operations has this transition form: ordinary "
                        + "computation changes local configuration, an original call changes the one actual "
                        + "pair and returns its fixed acknowledgement, and a read changes only local memory. "
                        + "There is no finite-state, fixed-horizon or uniform local-work premise.")),
                    Paragraph(Text(
                        "Run is the actual operational relation on natural pairs, including zero. Its event "
                        + "tape records local steps, completed actions and paid replies in chronological order. "
                        + "The terminal local configuration and actual endpoint are separate indices. A run "
                        + "may have no reads, may repeat the same read, and may perform arbitrary finite "
                        + "local computations and actions after its last read. All those actions remain in "
                        + "the terminal cumulative word.")),
                    Paragraph(Text(
                        "For an event tape E, records(A,E) pairs each reply with the complete chronological "
                        + "action word accumulated from A before that reply. Local steps produce no record; "
                        + "actions append a letter; each reply produces exactly one record. Empty words and "
                        + "repeated words are retained and charged. finalWord(A,E) includes all actions, "
                        + "including the final interval after the last reply. paidReads(E) counts reply events.")),
                    Paragraph(Text(
                        "The selector replays public code from its initial configuration using only acquired "
                        + "history. Between reads it runs local instructions and appends each action to a "
                        + "local cumulative-word buffer. At a requested read it selects that whole word as "
                        + "one reset query. It feeds the acquired answer into the same continuation and "
                        + "repeats. After the final answer it completes the remaining public interval before "
                        + "returning the original output. No unknown pair is simulated or consulted.")),
                    Paragraph(Text(
                        "Public interval evaluation uses StateTransition.eval, the usual partial execution "
                        + "of a deterministic transition function. normalize gives this partial operation an "
                        + "arbitrary total value on divergent histories. This totalization is noncomputable. "
                        + "On every actual prefix of a terminating run its value agrees with the finite "
                        + "public interpreter. The selector "
                        + "has no fuel, entry, stopping-time, tariff or backing-capacity input. No decision "
                        + "procedure for divergent histories or uniform bound on finite intervals is asserted.")),
                    Paragraph(Text(
                        "The proof follows each original local, action and read step. Deterministic public "
                        + "evaluation has the same endpoint before and after a silent step. The action-word "
                        + "invariant is x=runWord(A,v); appending an action updates both sides by that same "
                        + "original action. At a read, terminalGcd(H,A,v) is consequently the complete actual "
                        + "current gcd. The replayed instruction and its next local configuration coincide. "
                        + "Induction preserves all subsequent adaptive choices. At halt it preserves the "
                        + "output, final local state and entire action word, not only the acquired replies.")),
                    Paragraph(Text(
                        "For every run from initial state and entry v with tape E, terminal state t, endpoint "
                        + "y and output l, reset execution with the single selector and paidReads(E)+1 proof "
                        + "fuel returns exactly (records([],E),l). Normalized replay of that trace is "
                        + "(t,finalWord([],E)); y equals runWord(finalWord([],E),v); and the reset trace length "
                        + "equals paidReads(E). PublicRun proves that the public interpreter reproduces the entire same event tape, including each local step and action. The proof fuel certifies execution in the reset interface and "
                        + "is never passed to the selector. The same selector works for every entry."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("continuous-acquisition-lower-bound"),
                DeclarationHandle.Create(Prefix + "continuous_acquisition_lower_bound"),
                H("The exact reset optimum bounds the full continuous class"),
                StatementSource.FromAuthor(LowerStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix H at least one and one controller whose output type is ZMod(H) squared. "
                        + "Suppose that for every natural pair v there exists a terminating actual run "
                        + "outputting residueSource(H,v), with at most J paid replies. These run witnesses "
                        + "are per entry; their local step counts, action counts, tapes and termination "
                        + "times need not share a bound. Apply the transport to each run using the same "
                        + "public selector. Its exact traces and per-entry proof fuels witness that J "
                        + "belongs to TerminalGcdAcquisitionCost.acquisitionBudgets(H).")),
                    Paragraph(Text(
                        "The least-budget clause of terminal_gcd_acquisition_cost then gives "
                        + "(if H=1 then 0 else 2 costBound(H)) at most J. For H greater than one, "
                        + "costBound(H) is the maximum of h(p-1) over prime powers p^h exactly dividing H. "
                        + "The prime-axis arithmetic lower bound is reused without alteration. Identification "
                        + "alone suffices, so the inequality also applies to every successful identification "
                        + "and behavior-return competitor with retained callable service.")),
                    Paragraph(Text(
                        "This transport is a comparison of information interfaces, not a reset primitive "
                        + "for the actual continuous source. It proves no attaining return policy, positive "
                        + "closing construction, synchronized installed updater, source-service realization "
                        + "or upper resource bound. The original fixed acknowledgements, exclusive serial "
                        + "control, finite per-run service and backing, and exclusion of timing, failure, "
                        + "size or tariff observations are the interface conditions represented by Run. "
                        + "The simulated local computation is charged separately; only paid-read count "
                        + "is asserted to be preserved as an optimized resource."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Arith/FibonacciAtomic/TerminalGcdAcquisitionCost"))]));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string name, params Formula[] args) => Call(name, args);
    private static Formula Typed(string name, Formula type) =>
        Seq(Open, V(name), Sp, Colon, Sp, type, Close);
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula NatPair => Seq(Nat, Sp, Times, Sp, Nat);
    private static Formula Pair(Formula x, Formula y) => Seq(Open, x, Comma, Sp, y, Close);
    private static Formula Empty => Seq(OpenBracket, CloseBracket);
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula And(params Formula[] formulas) => Seq([.. formulas.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f })]);
    private static Formula TransportStatement()
    {
        var rec = C("records", Empty, V("E"));
        var word = C("finalWord", Empty, V("E"));
        return Seq(Forall, Sp, Typed("S", C("Type")), Sp, Typed("L", C("Type")), Sp,
            Typed("P", C("Controller", V("S"), V("L"))), Sp, Typed("H", Nat), Sp,
            Typed("E", C("List", C("Event"))), Sp, Typed("v", NatPair), Sp,
            Typed("t", V("S")), Sp, Typed("y", NatPair), Sp, Typed("l", V("L")), Comma, Sp,
            C("Run", V("P"), V("H"), C("initial", V("P")), V("v"), V("E"), V("t"), V("y"), V("l")),
            Sp, Implies, Sp, And(
                Eqn(C("execute", C("terminalGcd", V("H")), C("selector", V("P")),
                    Seq(C("paidReads", V("E")), Plus, D(1)), Empty, V("v")),
                    C("some", Pair(rec, V("l")))),
                Eqn(C("normalize", V("P"), C("replay", V("P"), rec)), Pair(V("t"), word)),
                Eqn(V("y"), C("runWord", word, V("v"))),
                Eqn(C("length", rec), C("paidReads", V("E"))),
                C("PublicRun", V("P"), Pair(C("initial", V("P")), Empty),
                    V("E"), Pair(V("t"), word), V("l"))));
    }
    private static Formula LowerStatement() => Seq(
        Forall, Sp, Typed("S", C("Type")), Sp, Typed("H", Nat), Sp,
        Typed("P", C("Controller", V("S"),
            Seq(C("ZMod", V("H")), Sp, Times, Sp, C("ZMod", V("H"))))), Sp,
        Typed("J", Nat), Comma, Sp,
        Seq(Open, D(1), Sp, Le, Sp, V("H"), Sp, Land, Sp,
            Open, Forall, Sp, Typed("v", NatPair), Comma, Sp,
            Exists, Sp, Typed("E", C("List", C("Event"))), Sp,
            Typed("t", V("S")), Sp, Typed("y", NatPair), Comma, Sp,
            And(C("Run", V("P"), V("H"), C("initial", V("P")), V("v"),
                    V("E"), V("t"), V("y"), C("residueSource", V("H"), V("v"))),
                Seq(C("paidReads", V("E")), Sp, Le, Sp, V("J"))),
            Close, Close), Sp, Implies, Sp,
        C("ite", Seq(V("H"), Eq, D(1)), D(0), Seq(D(2), C("costBound", V("H")))),
        Sp, Le, Sp, V("J"));
}
