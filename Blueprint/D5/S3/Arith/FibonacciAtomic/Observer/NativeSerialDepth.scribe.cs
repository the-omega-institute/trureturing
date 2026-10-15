using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSerialDepthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSerialDepth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSerialDepth", H("NativeSerialDepth"), Blocks(
            Entry("RowWord", "Finite whole-row output representation", "A finite list of optional Boolean-or-natural labels represents the complete row, including concrete exterior constructors and canonical hole class labels.", DescribeRole.Definition),
            Entry("rowWord", "Injective preorder row encoding", "Each leaf is one tagged label and each binary constructor is a separate marker. Prefix parsing proves injectivity without a tree-size bound; the encoding is used to transfer the original effective finite-output service to the complete canonical row.", DescribeRole.Definition),
            Entry("original_whole_row_implies_depth_and_image", "Full original-service depth and whole-output image", "The original selector simulation feeds the unrestricted native depth and prefix-free output-image theorems. The domain remains the entire ActualFiber, with one shared finite selector state at the actual epoch N and initial physical register substitution iterated N times on u. The common state may encode the complete retained row, task input, accessible workspace and any genuinely retained prior chronological record. It is not identified with H: H retains mixed-epoch Read constraints, while the selector appends the new chronological external suffix. Under original 59.3 the complete takeover state is a deterministic function of common input and R and recovers R; original 62.2 gives equal reached state on the same actual continuation record, and 74.1 exhausts accessible source information by U. Consequently this single state is common to the full fiber, rather than adding an extra producer-record filter. The frozen canonicalRow_record_iff, rowFiberEquiv and historyCellEquiv identify R with the complete exterior/full partition and H with its literal constraints, retaining all cross-class disequalities, repeated occurrences and absent guards. Producer acquisition records excluded by 59.3 are never reinstated. Certified N at least every historical epoch is an allowed specialization of this stronger unconstrained-N theorem. Injective finite row coding yields equality of whole canonicalRow and literalRecord, and at most four to the K terminal whole rows, including K zero and root/empty cuts. The proof-only image decoder supplies no runtime oracle. The original partial selector has sourcewise finite executions; no common local-work, runtime, update, workspace or address bound is assumed.", DescribeRole.Theorem),
            Entry("run_unique", "Labeled native trace and full-output uniqueness", "Two NativeSerialMachine.Run proofs from the same program, control, epoch and source have equal complete labeled traces and equal full outputs. The original statement and induction are preserved. OriginalVector.InterleavedWordRecovery consumes this theorem for the constructed vertex and word runs; it adds no execution interface or unlabeled halt semantics.", DescribeRole.Theorem),
            Entry("OriginalAgree", "Complete original-prefix agreement", "Agreement quantifies over every original address of length at most the given radius and uses the actual four-valued readout, including absence.", DescribeRole.Definition),
            Entry("descriptor", "Proof-only descriptor selection", "A finite replay, when it exists at a Read boundary, determines its unique epoch and physical address. A classical default on other words is used only to form a finite image. It supplies no effective stationary service.", DescribeRole.Definition),
            Entry("bounded_read_support", "Finite actual physical support", "Four-valued reply words of length strictly less than K form a finite set. Actual Read boundaries are uniquely determined by these words, so their physical epoch-address descriptors lie in one finite set. This does not assume finite control, a finite source fiber, bounded addresses or bounded update counts.", DescribeRole.Theorem),
            Entry("bounded_serial_original_depth", "Finite original observation depth", "Take the maximum address length in the finite physical support, with maximum zero for an empty support. All-epoch original-prefix locality makes every physical reply agree on sources with the same original prefix. Actual execution transfer then preserves the entire local/update/read trace and complete output. The radius can depend on the program, common input, fiber and initial epoch; no bound depending only on K and no common radius for all initial epochs is asserted.", DescribeRole.Theorem),
            Entry("whole_row_serial_implies_depth", "Whole actual row and record", "The domain is the entire NativeHistoryCells.ActualFiber of the complete old canonical row and mixed-epoch history. All old inequalities, repeated classes and absent-cut guards are retained by that interface. The conclusion concerns the complete new canonicalRow and the independently computed literalRecord, including exterior and whole partition. Arbitrary finite cuts, root and empty cuts, and finite nonempty fibers remain included. No ground-binding or unification premise occurs. The result is valid even without nonemptiness, and at every fixed actual common epoch.", DescribeRole.Theorem),
            Entry("effective_whole_row_implies_depth", "Encoded effective serial clause implies finite depth", "Apply the exact encoded-service inclusion to the full actual fiber and whole-row output. Sourcewise stopping and one uniform chronological Read budget then give precisely the finite-original-depth implication, without any stationary-service construction or other direction of the four-way classification.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeserialdepth-" + (name == "RowWord" ? "row-word-carrier" : name.Replace("_", "-").ToLowerInvariant())),
            DeclarationHandle.Create(Prefix + name), H(title),
            role == DescribeRole.Theorem ? StatementSource.FromAuthor(Disp(Statement(name))) : StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Statement(string name) => name switch
    {
        "original_whole_row_implies_depth_and_image" => All("S",Call("OriginalEffectiveService",V("RowWord")),All("s",V("OriginalState"),WholeInputs(Imp(EqOf(Call("epoch",V("s")),V("N")),Imp(Call("Nonempty",Fiber()),Imp(All("u",Fiber(),Some("t",V("Trace"),And(Call("OriginalRun",V("S"),V("s"),Call("iterate",V("substitution"),V("N"),Val("u")),V("t"),Call("rowWord",Row("u"))),Le(Len(Ans("t")),V("K"))))),And(WholeDepth(),Some("labels",Call("Finset",V("LiteralRow")),And(Le(Call("card",V("labels")),Call("pow",D(4),V("K"))),All("u",Fiber(),Mem(Row("u"),V("labels")))))))))))),
        "run_unique" => All("C,O", V("Type"), All("delta", Arr(V("C"), Call("Op", V("C"), V("O"))), All("c", V("C"), All("e", V("Nat"), All("r", V("Source"), All("t,s", V("Trace"), All("o,p", V("O"), Imp(And(Call("Run", V("delta"), V("c"), V("e"), V("r"), V("t"), V("o")), Call("Run", V("delta"), V("c"), V("e"), V("r"), V("s"), V("p"))), And(EqOf(V("t"), V("s")), EqOf(V("o"), V("p"))))))))))),
        "bounded_read_support" => Program(All("N,K",V("Nat"),Some("D",Call("Finset",V("Descriptor")),All("u",V("Source"),All("t",V("Trace"),All("o",V("O"),Imp(RunAt("u","t",V("o")),Imp(Le(Len(Ans("t")),V("K")),All("n",V("Nat"),All("a",V("Address"),All("y",V("Reply"),Imp(Mem(Call("ReadEvent",V("n"),V("a"),V("y")),V("t")),Mem(Tup(V("n"),V("a")),V("D")))))))))))))),
        "bounded_serial_original_depth" => Program(All("N,K",V("Nat"),All("U",Call("Set",V("Source")),All("F",Arr(V("Source"),V("O")),Imp(Correct(),Some("h",V("Nat"),All("u",V("Source"),Imp(Mem(V("u"),V("U")),All("v",V("Source"),Imp(Mem(V("v"),V("U")),Imp(Call("OriginalAgree",V("h"),V("u"),V("v")),And(EqOf(Call("F",V("u")),Call("F",V("v"))),Some("t",V("Trace"),And(RunAt("u","t",Call("F",V("u"))),RunAt("v","t",Call("F",V("v"))))))))))))))))),
        "whole_row_serial_implies_depth" => All("C",V("Type"),All("delta",Arr(V("C"),Call("Op",V("C"),V("LiteralRow"))),All("c",V("C"),WholeInputs(Imp(All("u",Fiber(),Some("t",V("Trace"),And(Call("Run",V("delta"),V("c"),V("N"),Call("iterate",V("substitution"),V("N"),Val("u")),V("t"),Row("u")),Le(Len(Ans("t")),V("K"))))),WholeDepth()))))),
        "effective_whole_row_implies_depth" => All("S",Call("EffectiveService",V("LiteralRow")),WholeInputs(Imp(All("u",Fiber(),Some("t",V("Trace"),And(Call("ServiceRun",V("S"),Call("initial",V("S")),V("N"),Call("iterate",V("substitution"),V("N"),Val("u")),V("t"),Row("u")),Le(Len(Ans("t")),V("K"))))),WholeDepth()))),
        _ => throw new ArgumentException(name)
    };

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f, i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Ans(string t) => Call("answers", V(t));
    private static Formula Len(Formula t) => Call("length", t);
    private static Formula Root(string e, string u) => Call("iterate", V("substitution"), V(e), V(u));
    private static Formula Tup(params Formula[] args) => Call("tuple", args);
    private static Formula RunAt(string root, string trace, Formula output) => Call("Run", V("delta"), V("c"), V("N"), Root("N",root), V(trace), output);
    private static Formula Program(Formula body) => All("C,O", V("Type"), All("delta", Arr(V("C"),Call("Op",V("C"),V("O"))), All("c",V("C"),body)));
    private static Formula Correct() => All("u",V("Source"),Imp(Mem(V("u"),V("U")),Some("t",V("Trace"),And(RunAt("u","t",Call("F",V("u"))),Le(Len(Ans("t")),V("K"))))));
    private static Formula Fiber() => Call("ActualFiber",V("P"),V("old"),V("H"));
    private static Formula Val(string u) => Call("value",V(u));
    private static Formula Row(string u) => Call("canonicalRow",V("Q"),Val(u));
    private static Formula Record(string u) => Call("literalRecord",V("Q"),Val(u));
    private static Formula WholeDepth() => Some("h",V("Nat"),All("u,v",Fiber(),Imp(Call("OriginalAgree",V("h"),Val("u"),Val("v")),And(EqOf(Row("u"),Row("v")),EqOf(Record("u"),Record("v"))))));
    private static Formula WholeInputs(Formula body) => All("P,Q",V("CutSet"),Imp(Call("CutPrefixFree",V("Q")),All("old",V("LiteralRow"),All("H",V("History"),All("N,K",V("Nat"),body)))));
}
