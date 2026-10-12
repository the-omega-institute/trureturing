using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFullSourceProducerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFullSourceProducer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One source-blind native stack program acquires and returns every finite source, retaining its full chronology and exact original node preorder.",
        H("Native Full Source Production"), Blocks(
            Entry("Frame", "Pending work and acquired subtrees", "A left frame stores a pending right-child address. A right frame stores the left subtree already constructed from actual replies. Frames contain no unknown input subtree.", DescribeRole.Definition),
            Entry("Control", "Unbounded source-free workspace", "Visit carries a literal address and a stack. Deliver carries an acquired subtree and its continuation stack. This carrier permits arbitrarily large finite stacks and acquired trees; the finite instruction description supplies no uniform finite carrier.", DescribeRole.Definition),
            Entry("sourceControl", "A fixed native instruction function", "Visit performs one NativeSerialMachine read. A leaf reply constructs its labelled leaf; a branch reply schedules the left child and saves the right address. Deliver switches to the pending right child or combines two acquired children using actual localStep instructions. An empty stack stops with the full acquired tree. The absent-reply branch makes the instruction function total; the proved runs never use it. Only local control is an argument: the unknown register, size, height, epoch, fuel and future tasks are absent.", DescribeRole.Definition),
            Entry("initialControl", "The common initial control", "Every input starts at Visit of the empty root address with an empty stack. It does not depend on the input source.", DescribeRole.Definition),
            Entry("productionTrace", "The complete native chronology", "The trace records a root read, then the left subtree, one local switch, the right subtree, and one local combination. A leaf contributes its single true read. Every event occurs at epoch zero and no update is issued. This tree-indexed trace describes the proved execution; it is not a runtime input or a stopping oracle.", DescribeRole.Definition),
            Entry("native_source_producer", "Exact sourcewise native termination", "For every finite Source, the same program terminates with that entire Source as output. Its nativeStep execution appends the complete productionTrace to any prior log, and every reachable configuration retains epoch zero and the initialized register. Retaining the read events and discarding the local-step markers yields exactly the existing acquisitionTrace with epoch-zero tags, in the original order and with the original replies. Its address list is exactly nodes, without duplicates, and its raw-call count is nodes.length. The proof's continuation invariant reconstructs a subtree into an arbitrary existing stack using actual read and localStep constructors. The preorder identity and absence of repeated nodes use ActualPureAcquisitionCompiler.trace_addresses and nodes_nodup. In the formula delta denotes sourceControl, initial denotes initialControl, T(U) denotes productionTrace [] U, H(U) denotes acquisitionTrace [] U, tagged tags each history entry with epoch zero, R(U) denotes reads(T(U)), A(U) maps each read to its address, epoch and register are configuration projections, tuple is the product constructor, append is list append, and Reaches is StateTransition.Reaches.", DescribeRole.Theorem),
            Paragraph(Text("Termination is pointwise over all finite inputs, with workspace and trace length allowed to grow with the replies actually acquired. It supplies no uniform raw-call bound. NativeSerialDepth.bounded_serial_original_depth and the criterion_failure_arbitrary_depth obstruction distinguish a uniformly bounded whole-row contract from this pointwise producer. The present construction has no Partrec certification, OriginalEffectiveService inclusion, later-task handoff, physical-fee bound or continuous complete-law realization. Those conclusions require their own interfaces."))
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("native-full-source-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title),
            role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement())) : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula Statement() => All("U", V("Source"), And(
        Call("Run", V("delta"), V("initial"), D(0), V("U"), T, V("U")),
        All("old", V("Trace"), Some("c", V("Control"), And(
            Reach(Tup(V("initial"), D(0), V("U"), V("old")), Tup(V("c"), D(0), V("U"), Call("append", V("old"), T))),
            EqOf(Call("delta", V("c")), Call("stop", V("U")))))),
        All("old", V("Trace"), All("x", Call("Config", V("Control")), Imp(
            Reach(Tup(V("initial"), D(0), V("U"), V("old")), V("x")),
            And(EqOf(Call("epoch", V("x")), D(0)), EqOf(Call("register", V("x")), V("U")))))),
        EqOf(R, Call("tagged", Call("H", V("U")))),
        EqOf(A, Call("nodes", V("U"))), Call("Nodup", A),
        EqOf(Call("length", R), Call("length", Call("nodes", V("U"))))));
    private static Formula V(string n) => F.Id(n);
    private static Formula T => Call("T", V("U"));
    private static Formula R => Call("R", V("U"));
    private static Formula A => Call("A", V("U"));
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string n, Formula t, Formula b) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Tup(params Formula[] args) => Call("tuple", args);
    private static Formula Reach(Formula a, Formula b) => Call("Reaches", Call("nativeStep", V("delta")), a, b);
}
