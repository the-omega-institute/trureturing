using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController;

internal sealed class RarePriorLiteralControllerLiveProducerSetupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/LiveProducerSetup.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController.LiveProducerSetup", H("Resident producer and physical current banks"), Blocks(
            Paragraph(Text("A producer retains the entire inherited address snapshot, native and service key rails, initialization, sampler, native and menu scanners, copied Runtime and Service words, finite stage, operation, ready role, raw service, reset probe, request and commit flags, and both input latches. Its injective code includes every retained component. The static image includes resident opcodes, rail end masks and service menu; the bound charges that image, the original program and the whole retained state together.")),
            Paragraph(Text("The actual and synthetic banks in CurrentBank are raw Boolean tapes. The role selects the sole mutable destination. The pre, query, payload, result and old-field tapes, row key, slot, offset, bank probe and latch, native scanner and resident-opcode motor coexist. Native key and payload bits are fetched from the installed physical tape, while fieldROM taps the copied pre-state. Address arithmetic and control resets remain atomic rail primitives.")),
            Paragraph(Text("The source and fresh-bit ports are distinct. Deterministic stages ignore both ports, and saved_cuts preserves the inherited retained snapshot at every finite cut. Codecs and decoded returned values are external observations, not transition inputs. The prepared producer below starts with a native key for the supplied Runtime; the unprepared physical-bank acquisition is the separate CurrentAcquisition result.")),
            Paragraph(Text("The native-key carry, scanner endpoint and literal Runtime-word copy are successive phases. ScannerSafe rules out a false successful row, graph_terminal handles absorbing outcomes, and motor_return supplies the copied tape at halt. The conclusion preserves addressed context, captured operation and the uncommitted flag through rendering entry. This finite path does not establish repeated full cycles, canonical Ready or a physical resource realization.")),
            Describe.Lean(DescribeId.Create("native-render"),
                DeclarationHandle.Create(Prefix + "native_render"), H("Native key reaches its copied return word"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A successful original runtimeStep is implemented from the stated native-key entry. The scanner result and literal tape copy produce the complete optional Runtime word; neither a successful scan nor a typed Runtime value is supplied as an instruction input."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/TransfersAddress"))]));

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
    private static Formula Word(Formula x) => App("word", x);
    private static Formula RuntimeWord(Formula x) => Word(App("runtimeCodec", x));
    private static Formula ResultWord(Formula x) => Word(App("optionalRuntimeCodec", App("some", x)));
    private static Formula PState => Seq(N("LiveProducer"), Dot, N("State"));
    private static Formula LP(string name) => Seq(N("LiveProducer"), Dot, N(name));

    private static Formula Statement()
    {
        var p = N("p"); var z = N("z"); var op = N("op"); var d = N("d"); var a = N("a");
        var operation = App("operationCodec", op);
        var end = And(EqF(AppF(LP("run"), p, D(0), D(0), N("t")), a),
            EqF(Field(a, "stage"), Seq(LP("Stage"), Dot, N("render"))),
            EqF(Field(a, "runtime", "tape"), ResultWord(d)),
            EqF(Field(a, "addressed"), Field(p, "addressed")),
            EqF(Field(a, "operation"), operation), EqF(Field(a, "committed"), N("false")));
        var result = Assuming(Some("t", Nat, Some("a", PState, end)),
            EqF(Field(p, "stage"), Seq(LP("Stage"), Dot, N("nativeKey"))),
            EqF(Field(p, "nativeKey"), App("keyEntry", RuntimeWord(z), operation)),
            EqF(Field(p, "runtime"), App("motorEntry", Seq(N("runtimeSize"), Plus, D(1)))),
            EqF(Field(p, "operation"), operation), EqF(Field(p, "committed"), N("false")),
            EqF(App("runtimeStep", z, op), App("some", d)));
        return All("p", PState, All("z", N("Runtime"), All("op", N("Operation"), All("d", N("Runtime"), result))));
    }
}
