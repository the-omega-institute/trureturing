using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController;

internal sealed class RarePriorLiteralControllerLiveProducerWorkDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController.LiveProducerWork", H("Physical-bank query and successor writeback"), Blocks(
            Paragraph(Text("The current bank is first copied to the pre tape and then encoded by the literal key carry into the raw unary query. bank_query identifies that query with nativeKey for the bank-encoded Runtime and captured operation. build_key_work preserves the pre, result and old-field work, row slot and offset through the carry phase.")),
            Paragraph(Text("PayloadGood is a proof invariant relating the scanner row and accumulator to a copied unary payload. installed_payload_step reads the installed physical program, establishes the next payload invariant and refines installedGraphStep. The nativeTable appears in this specification; the transition obtains each payload bit from nativeBit on the installed tape.")),
            Paragraph(Text("Writeback alternates a read from the copied result tape and a write to the role-selected bank. writeCheckpoint fixes every already written prefix and retains the remaining bank cells. The write-cycle and write-prefix inductions include the exhausted boundary, and result_drop removes only the optional-result marker before writing the complete successor Runtime.")),
            Paragraph(Text("The displayed endpoint starts at phase nine with bankProbe zero and the complete successful result tape. It reaches phase eleven with exactly the selected successor bank and the opposite bank preserved. Operation, role and outer image context stay fixed, and writeback emits no frame bits. Phase eleven retains work; it does not assert canonical Ready or a complete repeated service cycle.")),
            Describe.Lean(DescribeId.Create("write-complete"),
                DeclarationHandle.Create(Prefix + "write_complete"), H("Complete bitwise writeback with a quiet trace"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two-instruction per-cell schedule writes every Runtime bit, then the exhausted probe retires. The proof keeps both physical banks in the statement and shows the entire output trace is empty during this phase."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerExecution"))]));

    private static Formula N(string x) => Seq(Operatorname, Grp(F.Id(x)));
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula App(string name, params Formula[] args) => AppF(N(name), args);
    private static Formula AppF(Formula name, params Formula[] args)
    {
        var pieces = new System.Collections.Generic.List<Formula> { name, Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) pieces.Add(Seq(Comma, Sp));
            pieces.Add(args[i]);
        }
        pieces.Add(Close);
        return F.Seq(pieces.ToArray());
    }
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Field(Formula a, params string[] names)
    {
        foreach (var name in names) a = Seq(Open, a, Close, Dot, N(name));
        return a;
    }
    private static Formula And(params Formula[] xs)
    {
        var r = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--)
            r = Seq(Open, Open, xs[i], Close, Sp, Land, Sp, Open, r, Close, Close);
        return r;
    }
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Assuming(Formula body, params Formula[] assumptions)
    {
        for (var i = assumptions.Length - 1; i >= 0; i--) body = Arrow(assumptions[i], body);
        return body;
    }
    private static Formula If(Formula test, Formula yes, Formula no) =>
        Seq(Open, N("if"), Sp, test, Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no, Close);
    private static Formula Word(Formula x) => App("word", x);
    private static Formula RuntimeWord(Formula x) => Word(App("runtimeCodec", x));
    private static Formula ResultWord(Formula x) => Word(App("optionalRuntimeCodec", App("some", x)));
    private static Formula CState => Seq(N("LiveProducer"), Dot, N("CurrentBank"), Dot, N("State"));
    private static Formula CB(string name) => Seq(N("LiveProducer"), Dot, N("CurrentBank"), Dot, N(name));
    private static Formula Statement()
    {
        var s = N("s"); var d = N("d"); var q = N("q"); var role = Field(s, "role");
        var end = And(EqF(AppF(CB("run"), s, N("t")), q), EqF(Field(q, "phase"), D(1,1)),
            EqF(Field(q, "actual"), If(role, Field(s, "actual"), RuntimeWord(d))),
            EqF(Field(q, "synthetic"), If(role, RuntimeWord(d), Field(s, "synthetic"))),
            EqF(Field(q, "operation"), Field(s, "operation")),
            EqF(Field(q, "role"), role), EqF(Field(q, "addressed", "outer"), Field(s, "addressed", "outer")),
            EqF(AppF(CB("trace"), s, N("t")), Seq(OpenBracket, CloseBracket)));
        return All("s", CState, All("d", N("Runtime"), Assuming(Some("t", Nat, Some("q", CState, end)),
            EqF(Field(s, "phase"), D(9)), EqF(Field(s, "bankProbe"), D(0)),
            EqF(Field(s, "result", "tape"), ResultWord(d)))));
    }
}
