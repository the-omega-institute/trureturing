using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController;

internal sealed class RarePriorLiteralControllerLiveProducerRenderingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerRendering.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController.LiveProducerRendering", H("Six original frame words and selected-bank commit"), Blocks(
            Paragraph(Text("The installed scanner cycles pay for resident-opcode copying before each native scan step. scan_exit combines the scanner refinement and PayloadGood invariant with the successful native result. result_exit and fields_exit then copy the successful payload and the original pre-state fields; prepare_event reaches the original event-row key.")),
            Paragraph(Text("Each row key is fieldsCodec times twenty-four plus the captured operation times six plus the slot. The address motor reads the installed frame bit at the current offset. row_emit and offset_emit advance through the entire frameWidth. finish_frame completes the current frame at phase eight while preserving its slot; render_remaining advances between slots, and render_all orders all six frame words. These are actual transition and trace equalities; the chronological slot and offset coordinates remain external proof parameters.")),
            Paragraph(Text("The result below requires rendering entry at phase five, slot and offset zero, the exact encoded old fields, matching row key, captured operation, installed program and the complete successful successor-result tape. It first emits the flattened six frame codes in increasing slot order and then performs quiet selected-bank writeback. The opposite bank, operation, role and outer installation context are retained.")),
            Paragraph(Text("preparing_quiet excludes output before rendering. For an execution that reaches phase eleven, retired_no_fault excludes phase twelve at every cut. render_commit preserves the outer installation context at its endpoint. Phase eleven is a retained-work endpoint; a canonical Ready reset, repeated full cycles, live fresh service, full-tail readout, COMPLETE membership and the full-class risk, radius and threshold claims are outside this result.")),
            Describe.Lean(DescribeId.Create("render-commit"),
                DeclarationHandle.Create(Prefix + "render_commit"), H("Exact six-frame stream followed by bank writeback"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The frame sequence is determined by the same original fields and operation as the row key. Its full bit trace survives concatenation with the quiet writeback trace, and both bank equations remain in the conclusion."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerWork"))]));

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
        var s = N("s"); var z = N("z"); var d = N("d"); var op = N("op"); var q = N("q");
        var role = Field(s, "role"); var old = Word(App("fieldsCodec", Field(z, "fields")));
        var key = Seq(Langle, Field(s, "operation", "val"), Star, D(6), Plus, Field(s, "slot", "val"), Rangle);
        var frame = App("bitCode", App("frameCodec", App("eventROM", Field(z, "fields"), op, N("slot"))));
        var six = Field(AppF(Seq(N("List"), Dot, N("ofFn")), Seq(Open, N("fun"), Sp, N("slot"), Sp, Colon, Sp,
            App("Fin", D(6)), Sp, Mapsto, Sp, frame, Close)), "flatten");
        var end = And(EqF(AppF(CB("run"), s, N("t")), q), EqF(Field(q, "phase"), D(1,1)),
            EqF(Field(q, "actual"), If(role, Field(s, "actual"), RuntimeWord(d))),
            EqF(Field(q, "synthetic"), If(role, RuntimeWord(d), Field(s, "synthetic"))),
            EqF(Field(q, "operation"), Field(s, "operation")), EqF(Field(q, "role"), role),
            EqF(Field(q, "addressed", "outer"), Field(s, "addressed", "outer")),
            EqF(AppF(CB("trace"), s, N("t")), six));
        return All("s", CState, All("z", N("Runtime"), All("d", N("Runtime"), All("op", N("Operation"),
            Assuming(Some("t", Nat, Some("q", CState, end)), EqF(Field(s, "phase"), D(5)),
                EqF(Field(s, "operation"), App("operationCodec", op)),
                EqF(Field(s, "addressed", "outer", "installation", "tape"), N("programTape")),
                EqF(Field(s, "row"), App("keyEntry", old, key)), EqF(Field(s, "fields", "tape"), old),
                EqF(Field(s, "offset", "val"), D(0)), EqF(Field(s, "slot"), D(0)),
                EqF(Field(s, "result", "tape"), ResultWord(d)))))));
    }
}
