using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition;

internal sealed class NativeSelectedRAProgressDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeSelectedRAProgress.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cursors remain meaningful during independent source substitution.",
        H("Native scanner frontiers"), Blocks(
            Paragraph(Text("The source register is an arbitrary finite ordered binary tree. "
                + "A writer event substitutes every leaf while leaving the observer's whole configuration unchanged. "
                + "An observer event executes one actual read, one private instruction or the separate Return. "
                + "The schedule may interleave these events at every instruction.")),
            Def("PairPresent", "Two existing positions",
                "For a relative cursor z, both positions Lz and Rz have nonabsent replies in the current source."),
            Def("PairBranch", "Two branch positions",
                "Both positions Lz and Rz are current branches. Either common child extends the relative cursor to two existing positions."),
            Def("Saved", "A saved reply under substitution",
                "A saved reply is nonabsent, and a saved branch still denotes a branch at its original address. A saved leaf label need not equal the current reply."),
            Def("Frontier", "Concrete phase conditions",
                "Guard search reads an existing address and descends only after a branch. "
                + "Comparison phases distinguish the left and right base cells, existing paired positions, saved replies and branch positions before descent. "
                + "An upward cursor may name a completed subtree whose leaves have since grown. "
                + "Cleanup records the regions and latches already cleared; reset reaches an empty guard address before starting the next search. "
                + "The error control numbered ninety nine is excluded."),
            Def("Safe", "The whole configuration",
                "Entry and ready configurations satisfy the condition. An active configuration satisfies exactly its current source dependent frontier condition."),
            Describe.Lean(DescribeId.Create("native-selected-ra-reachable-frontier"),
                DeclarationHandle.Create(Prefix + "reachable_scan_frontier"),
                H("Every actual prefix has a valid frontier"), StatementSource.FromAuthor(Reachable()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every source, schedule and finite prefix, the actual register and configuration satisfy Safe. "
                    + "Every active configuration therefore has control different from ninety nine. "
                    + "The induction follows actual writer and observer events. Existing addresses and branches survive substitution. "
                    + "The comparison can descend only through two saved branches; upward retraction exposes a parent branch before the sibling switch."))),
                DescribeRole.Theorem),
            Def("ScanFinishes", "A finite stationary comparison continuation",
                "The current whole configuration has a finite update-free continuation to an active Work configuration at control eight. The continuation composes with every subsequent returning execution. It preserves the actual current source; it imposes no bound on tree size, cursor length or earlier interference."),
            Describe.Lean(DescribeId.Create("native-selected-ra-reachable-frontier-progress"),
                DeclarationHandle.Create(Prefix + "reachable_scan_frontier_progress"),
                H("Resuming every reachable comparison phase"), StatementSource.FromAuthor(Progress()),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "Every finite actual prefix has a safe frontier. If its control is twenty, twenty one, twenty two, twenty three, twenty four, twenty six, twenty seven, twenty eight or thirty one, its comparison resumes to control eight on the actual current source. "
                    + "A saved branch remains an actual branch after substitution, so an interrupted read pair can safely finish its decision. "
                    + "The stationary equal and unequal subtree scans handle each pending subtree. Reverse induction on the cursor handles upward retraction and the next right sibling. "
                    + "This conclusion concerns the comparison phase; guard search, validation, retry and final handoff are separate phases."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-selected-ra-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string n) => F.Id(n);
    private static Formula Op(string n) => Seq(Operatorname, Grp(V(n)));
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Op(n), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula type, Formula body) =>
        Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Progress()
    {
        Formula w = Call("trajectory", V("s"), Call("world", Op("entry"), V("u"), Op("false")), V("n"));
        Formula controls = Seq(OpenBracket, D(2,0), Comma, D(2,1), Comma, D(2,2), Comma,
            D(2,3), Comma, D(2,4), Comma, D(2,6), Comma, D(2,7), Comma, D(2,8), Comma, D(3,1), CloseBracket);
        Formula phase = Seq(Call("control", V("r")), Sp, InMacro, Sp, controls);
        Formula conclusion = Call("ScanFinishes", Call("source", w), Call("active", V("q"), V("r")));
        Formula active = All("q", Op("Bool"), All("r", Op("Work"),
            Seq(Par(EqOf(Call("config", w), Call("active", V("q"), V("r")))), Sp, Implies, Sp,
                Par(Seq(Par(phase), Sp, Implies, Sp, conclusion)))));
        return Disp(All("u", Op("Source"), All("s", Seq(Op("Nat"), Sp, To, Sp, Op("Bool")),
            All("n", Op("Nat"), Seq(Call("Safe", Call("source", w), Call("config", w)), Sp, Land, Sp, Par(active))))));
    }
    private static Formula Reachable()
    {
        Formula w = Call("trajectory", V("s"), Call("world", Op("entry"), V("u"), Op("false")), V("n"));
        Formula active = All("q", Op("Bool"), All("r", Op("Work"),
            Seq(Par(EqOf(Call("config", w), Call("active", V("q"), V("r")))), Sp, Implies, Sp,
                Par(Seq(Call("control", V("r")), Sp, Neq, Sp, D(9,9))))));
        return Disp(All("u", Op("Source"), All("s", Seq(Op("Nat"), Sp, To, Sp, Op("Bool")),
            All("n", Op("Nat"), Seq(Call("Safe", Call("source", w), Call("config", w)), Sp, Land, Sp, Par(active))))));
    }
}
