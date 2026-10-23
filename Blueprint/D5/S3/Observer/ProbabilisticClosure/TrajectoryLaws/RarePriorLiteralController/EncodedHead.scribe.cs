using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.RarePriorLiteralController;

internal sealed class RarePriorLiteralControllerEncodedHeadDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorLiteralController/EncodedHead.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "RarePriorLiteralController.EncodedHead", H("Encoded-head finite ROM execution"), Blocks(
            Paragraph(Text("The head is an encoded finite tape. Its literal scan, carry, read, write and emit instructions implement the ROM copy checkpoints, including paused cuts and permanent halt at the exhausted width.")),
            Node("encoded-head-copy-refinement", "encoded_head_copy_refinement", "Encoded head at every paused instruction",
                "For every finite ROM, the actual head-bit scan and carry execution reaches the exact macro checkpoint tape and trace, preserves all residual instruction cuts, copies the complete tape and reaches a permanent halt.")),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/NativeFullResidual")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode"))]));

    private static Formula App(string name, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Comma, Sp));
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return F.Seq(terms.ToArray());
    }
    private static Formula N(string name)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        var parts = name.Split('.');
        for (var i = 0; i < parts.Length; i++)
        {
            if (i > 0) terms.Add(Dot);
            terms.Add(Seq(Operatorname, Grp(F.Id(parts[i]))));
        }
        return F.Seq(terms.ToArray());
    }
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula ListOf(Formula x) => App("List", x);
    private static Formula FinOf(Formula x) => App("Fin", x);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula EqF(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Open, Open, a, Close, Sp, Land, Sp, Open, b, Close, Close);
    private static Formula Add(Formula a, Formula b) => Seq(a, Plus, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Star, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Leq, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Lt, b);
    private static Formula Field(Formula x, string s) => Seq(Open, x, Close, Dot, N(s));
    private static Formula Fn(string x, Formula ty, Formula body) =>
        Seq(Open, N("fun"), Sp, N(x), Sp, Colon, Sp, ty, Sp, Mapsto, Sp, body, Close);
    private static Formula Pair(Formula a, Formula b, Formula c) =>
        Seq(Open, a, Comma, b, Comma, c, Close);
    private static Formula With(Formula x, string f, Formula value) =>
        Seq(OpenBrace, x, Sp, N("with"), Sp, N(f), Sp, Colon, Eq, Sp, value, CloseBrace);
    private static Formula Iter(Formula fn, Formula ticks, Formula state) =>
        Seq(Open, fn, Close, Caret, Grp(Seq(OpenBracket, ticks, CloseBracket)), Sp, state);
    private static Formula Cp(Formula rom, Formula m, Formula hm) => App("copyCheckpoint", rom, m, hm);
    private static Formula Run(Formula rom, Formula start, Formula ticks) => App("copyRun", rom, start, ticks);
    private static Formula Trace(Formula rom, Formula start, Formula ticks) => App("copyTrace", rom, start, ticks);
    private static Formula PrefixBits(Formula rom, Formula m) =>
        App("List.ofFn", Fn("i", FinOf(m), App("rom", App("Fin.castLE", N("hm"), N("i")))));
    private static Formula Frame(Formula f, Formula op, Formula slot) => App("eventROM", f, op, slot);
    private static Formula Rom(Formula f, Formula op, Formula slot) => App("frameTape", Frame(f, op, slot));
    private static Formula Decoded(Formula f, Formula op) =>
        App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame",
                Trace(Rom(f, op, N("slot")), N("renderFrame"), Mul(D(4), N("frameWidth"))))))));
    private static Formula InstalledDecoded(Formula state) =>
        App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame",
                Trace(App("installedFrameROM", App("installed", state), N("slot")),
                    N("renderFrame"), Mul(D(4), N("frameWidth"))))))));
    private static Formula CopyConclusion()
    {
        var rom = N("rom"); var w = N("w"); var m = N("m"); var r = N("r");
        var cp = Cp(rom, m, N("hm")); var start = App("copyEntry", w);
        var ticks = Add(Mul(D(4), m), r);
        var equality = And(EqF(Run(rom, start, ticks), Run(rom, cp, r)),
            EqF(Trace(rom, start, ticks), Seq(PrefixBits(rom, m), Sp, Plus, Plus, Sp, Trace(rom, cp, r))));
        var paused = All("m", Nat, All("hm", Le(m, w), All("r", Nat, equality)));
        var installed = EqF(Field(Run(rom, start, Mul(D(4), w)), "tape"), rom);
        var stopped = All("n", Nat, EqF(Run(rom, start, Add(Add(Mul(D(4), w), D(1)), N("n"))),
            With(Cp(rom, w, Seq(N("le"), Underscore, Grp(N("rfl")))), "pc", N("CopyPC.halt"))));
        return And(paused, And(installed, stopped));
    }

    private static DocumentBlock.Describe Node(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Statement(string name) => name switch
    {
        "current_bank_paid_core_return" => CurrentBankCoreReturn(),
        "current_bank_original_frames" => CurrentBankFrames(),
        "current_bank_native_payload" => CurrentBankPayload(),
        "current_bank_paid_fetch" => CurrentBankFetch(),
        "tagged_source_commit" => TaggedSourceCommit(),
        "charged_address_execution" => LiteralAddress(),
        "charged_literal_transfers" => LiteralTransfers(),
        "encoded_head_copy_refinement" => MotorRefinement(),
        "six_slot_original_events" => SixSlots(),
        "paused_copy_refinement" => All("w", Nat, All("rom", Arrow(FinOf(N("w")), N("Bool")), CopyConclusion())),
        "streamed_original_events" => StreamedEvents(),
        "charged_installed_frames" => ChargedFrames(),
        "streamed_original_history" => StreamedHistory(),
        _ => throw new System.InvalidOperationException(name)
    };

    private static Formula Both(params Formula[] xs)
    {
        var result = xs[^1];
        for (var i = xs.Length - 2; i >= 0; i--) result = And(xs[i], result);
        return result;
    }
    private static Formula Some(Formula x) => App("some", x);
    private static Formula Ex(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula CurrentBankCoreReturn()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var r = N("r"); var cur = Field(Field(r, "current"), "current"); var t = N("t");
        var outer = Field(Field(cur, "addressed"), "outer");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        Formula Select(Formula yes, Formula no) => Seq(Open, N("if"), Sp, role,
            Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no, Close);
        var next = Word(App("runtimeCodec", d));
        var start = App("LiveProducer.Return.entry", App("LiveProducer.Current.entry",
            saved, image, a, c, role, App("operationCodec", op)));
        var round = All("w", N("Runtime"), Arrow(
            EqF(Field(cur, "actual"), Word(App("runtimeCodec", N("w")))),
            App("LiveProducer.Return.NextRound", r, N("w"))));
        var endpoint = Ex("t", Nat, Ex("r", N("LiveProducer.Return.State"), Both(
            EqF(App("LiveProducer.Return.run", start, D(0), D(0), t), r),
            EqF(r, App("LiveProducer.Return.coreReady", saved, outer, Select(a, next), Select(next, c))),
            EqF(Field(Field(outer, "installation"), "tape"), N("programTape")), round)));
        var charge = All("s", N("LiveProducer.Return.State"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("LiveProducer.Return.staticImage"), "length")),
                Field(App("LiveProducer.Return.code", N("s")), "length")), N("LiveProducer.Return.bound")));
        var ports = Arrow(EqF(App("LiveProducer.Return.actualRequest", N("q")), N("false")),
            EqF(App("LiveProducer.Return.step", N("q"), N("x"), N("y")),
                App("LiveProducer.Return.step", N("q"), N("u"), N("v"))));
        foreach (var name in new[] { "v", "u", "y", "x" }) ports = All(name, N("Letter"), ports);
        ports = All("q", N("LiveProducer.Return.State"), ports);
        var body = Both(App("Function.Injective", N("LiveProducer.Return.code")), charge, ports, endpoint);
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(Select(c, a), Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankFrames()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var p = N("p"); var q = N("q"); var pc = Field(p, "current"); var qc = Field(q, "current");
        var tp = N("tp"); var tr = N("tr");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        Formula Select(Formula yes, Formula no) => Seq(Open, N("if"), Sp, role,
            Sp, N("then"), Sp, yes, Sp, N("else"), Sp, no, Close);
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role,
            App("operationCodec", op));
        var next = Word(App("runtimeCodec", d));
        var frames = Field(App("List.ofFn", Fn("slot", FinOf(D(6)), App("bitCode",
            App("frameCodec", App("eventROM", Field(z, "fields"), op, N("slot")))))), "flatten");
        var bankStart = App("LiveProducer.CurrentBank.entry", image, a, c, role, App("operationCodec", op));
        var paused = All("k", Nat, Arrow(Le(N("k"), Add(tp, tr)),
            Ex("suffix", ListOf(N("Bool")), EqF(frames,
                Seq(App("LiveProducer.CurrentBank.trace", bankStart, N("k")), Sp,
                    Plus, Plus, Sp, N("suffix"))))));
        var cut = App("LiveProducer.CurrentBank.run", bankStart, N("n"));
        var cuts = All("n", Nat, And(
            Seq(Field(cut, "phase"), Sp, Neq, Sp, D(1,2)),
            Arrow(EqF(role, N("true")), EqF(Field(cut, "actual"), a))));
        var decoded = App("List.map", N("original"), App("List.filterMap", N("id"),
            App("List.ofFn", Fn("slot", FinOf(D(6)), App("decodeFrame", App("bitCode",
                App("frameCodec", App("eventROM", Field(z, "fields"), op, N("slot")))))))));
        var acquired = App("LiveProducer.Current.step",
            App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y"));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            Arrow(EqF(role, N("false")), Arrow(EqF(op, App("Operation.read", N("x"))),
                EqF(App("LiveProducer.Current.run", acquired, D(0), D(0), Add(tp, tr)), q)))));
        var body = Ex("tp", Nat, Ex("p", N("LiveProducer.Current.State"),
            Ex("tr", Nat, Ex("q", N("LiveProducer.Current.State"), Both(
                EqF(App("LiveProducer.Current.run", start, D(0), D(0), tp), p),
                EqF(Field(p, "acquiring"), N("false")), EqF(Field(pc, "phase"), D(5)),
                EqF(App("LiveProducer.Current.run", p, D(0), D(0), tr), q),
                EqF(Field(qc, "phase"), D(1,1)),
                EqF(Field(qc, "actual"), Select(a, next)),
                EqF(Field(qc, "synthetic"), Select(next, c)),
                EqF(Field(qc, "operation"), App("operationCodec", op)),
                EqF(Field(qc, "role"), role),
                EqF(Field(Field(Field(qc, "addressed"), "outer"), "installation.tape"), N("programTape")),
                EqF(App("LiveProducer.CurrentBank.trace", pc, tr), frames),
                EqF(App("LiveProducer.CurrentBank.trace",
                    App("LiveProducer.CurrentBank.entry", image, a, c, role, App("operationCodec", op)),
                    Add(tp, tr)), frames), paused, cuts,
                EqF(decoded, App("eventBlock", Field(z, "fields"), op)), acquisition)))));
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(Select(c, a), Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankPayload()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var d = N("d"); var op = N("op");
        var q = N("q"); var cur = Field(q, "current"); var t = N("t");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        Formula Word(Formula x) => App("LiveProducer.word", x);
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role,
            App("operationCodec", op));
        var payload = Word(App("optionalRuntimeCodec", Some(d)));
        var fields = Word(App("fieldsCodec", Field(z, "fields")));
        var operation = App("operationCodec", op);
        var tail = Seq(Langle, Sp, Mul(Field(operation, "val"), D(6)), Sp, Rangle);
        var acquired = App("LiveProducer.Current.step",
            App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y"));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            Arrow(EqF(role, N("false")), Arrow(EqF(op, App("Operation.read", N("x"))),
                EqF(App("LiveProducer.Current.run", acquired, D(0), D(0), t), q)))));
        var returned = N("r"); var returnedCurrent = Field(returned, "current");
        var emits = Ex("n", Nat, Ex("r", N("LiveProducer.Current.State"), Both(
            EqF(App("LiveProducer.Current.run", q, D(0), D(0), N("n")), returned),
            EqF(Field(returnedCurrent, "phase"), D(7)),
            EqF(App("LiveProducer.Current.output", returned),
                Some(App("frameTape", App("eventROM", Field(z, "fields"), op, D(0)), D(0)))),
            EqF(Field(returnedCurrent, "actual"), a),
            EqF(Field(returnedCurrent, "synthetic"), c))));
        var body = Ex("t", Nat, Ex("q", N("LiveProducer.Current.State"), Both(
            EqF(App("LiveProducer.Current.run", start, D(0), D(0), t), q),
            EqF(Field(q, "acquiring"), N("false")), EqF(Field(cur, "phase"), D(5)),
            EqF(Field(cur, "payload"), payload), EqF(Field(Field(cur, "native"), "pc"), D(2)),
            EqF(Field(cur, "actual"), a), EqF(Field(cur, "synthetic"), c),
            EqF(Field(cur, "operation"), operation), EqF(Field(cur, "role"), role),
            EqF(Field(Field(Field(cur, "addressed"), "outer"), "installation.tape"), N("programTape")),
            EqF(Field(Field(cur, "result"), "tape"), payload),
            EqF(Field(Field(cur, "pre"), "tape"), Word(App("runtimeCodec", z))),
            EqF(Field(Field(cur, "fields"), "tape"), fields),
            EqF(Field(cur, "slot"), D(0)), EqF(Field(Field(cur, "offset"), "val"), D(0)),
            EqF(Field(cur, "row"), App("LiveProducer.keyEntry", fields, tail)), acquisition, emits)));
        var selected = Seq(Open, N("if"), Sp, role, Sp, N("then"), Sp, c,
            Sp, N("else"), Sp, a, Close);
        body = Arrow(EqF(App("runtimeStep", z, op), Some(d)), body);
        body = Arrow(EqF(selected, Word(App("runtimeCodec", z))), body);
        body = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")), body);
        body = All("op", N("Operation"), body);
        body = All("d", N("Runtime"), body); body = All("z", N("Runtime"), body);
        body = All("role", N("Bool"), body);
        body = All("c", bankType, body); body = All("a", bankType, body);
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), body));
    }

    private static Formula CurrentBankFetch()
    {
        var saved = N("saved"); var image = N("image"); var a = N("a"); var c = N("c");
        var role = N("role"); var z = N("z"); var op = N("op"); var q = N("q");
        var cur = Field(q, "current"); var t = N("t");
        var bankType = Arrow(FinOf(N("runtimeSize")), N("Bool"));
        var producer = N("LiveProducer.Current.State"); var bank = N("LiveProducer.CurrentBank.State");
        Formula Word(Formula x) => App("LiveProducer.word", x);
        var query = Word(App("nativeKeyCodec", Seq(Open, z, Comma, op, Close)));
        var start = App("LiveProducer.Current.entry", saved, image, a, c, role, App("operationCodec", op));
        var selected = Seq(Open, N("if"), Sp, role, Sp, N("then"), Sp, c, Sp, N("else"), Sp, a, Close);
        var fetched = Ex("t", Nat, Ex("q", producer, Both(
            EqF(App("LiveProducer.Current.run", start, D(0), D(0), t), q),
            EqF(Field(q, "acquiring"), N("false")), EqF(Field(cur, "phase"), D(2)),
            EqF(Field(cur, "query"), query),
            EqF(Field(cur, "native"), App("scannerEntry", App("nativeKeyCodec", Seq(Open, z, Comma, op, Close)))),
            EqF(Field(Field(cur, "opcodes"), "tape"), App("LiveProducer.CurrentBank.opcodeTape", D(0))),
            EqF(Field(cur, "actual"), a), EqF(Field(cur, "synthetic"), c),
            EqF(Field(cur, "operation"), App("operationCodec", op)), EqF(Field(cur, "role"), role),
            EqF(Field(Field(Field(cur, "addressed"), "outer"), "installation.tape"), N("programTape")))));
        var preparation = Arrow(EqF(Field(Field(image, "installation"), "tape"), N("programTape")),
            Arrow(EqF(selected, Word(App("runtimeCodec", z))), fetched));
        var native = Field(q, "native");
        var scanner = All("q", bank, Arrow(
            EqF(Field(Field(Field(q, "addressed"), "outer"), "installation.tape"), N("programTape")),
            Arrow(EqF(Field(q, "query"), Word(Field(native, "query"))),
            Arrow(EqF(Field(Field(q, "opcodes"), "tape"), App("LiveProducer.CurrentBank.opcodeTape", Field(native, "pc"))),
                EqF(Field(App("LiveProducer.CurrentBank.scanStep", q), "native"),
                    App("installedGraphStep", N("nativeTable"), native))))));
        var preserve = All("q", bank, All("n", Nat, Arrow(EqF(Field(q, "role"), N("true")),
            EqF(Field(App("LiveProducer.CurrentBank.run", q, N("n")), "actual"), Field(q, "actual")))));
        var r = N("r"); var d = N("d");
        var writing = All("q", bank, All("d", N("Runtime"), Arrow(EqF(Field(q, "phase"), D(9)),
            Arrow(EqF(Field(q, "bankProbe"), D(0)),
            Arrow(EqF(Field(Field(q, "result"), "tape"), Word(App("optionalRuntimeCodec", Some(d)))),
                Ex("t", Nat, Ex("r", bank, Both(
                    EqF(App("LiveProducer.CurrentBank.run", q, t), r), EqF(Field(r, "phase"), D(1,1)),
                    EqF(App("LiveProducer.CurrentBank.bank", r), Word(App("runtimeCodec", d))),
                    EqF(Field(r, "operation"), Field(q, "operation")),
                    Arrow(EqF(Field(q, "role"), N("true")), EqF(Field(r, "actual"), Field(q, "actual")))))))))));
        var fields = All("q", bank, Arrow(EqF(Field(Field(q, "pre"), "tape"), Word(App("runtimeCodec", z))),
            EqF(App("LiveProducer.CurrentBank.fieldROM", q), Word(App("fieldsCodec", Field(z, "fields"))))));
        var charge = All("q", producer, LtF(Add(Add(Field(N("programImage"), "length"),
            Field(N("LiveProducer.Current.staticImage"), "length")), Field(App("LiveProducer.Current.code", q), "length")), N("LiveProducer.Current.bound")));
        var acquisition = All("x", N("Letter"), All("y", N("Letter"),
            EqF(App("LiveProducer.Current.step", App("LiveProducer.Current.sourceEntry", saved, image, a, c), N("x"), N("y")),
                App("LiveProducer.Current.entry", saved, image, a, c, N("false"), App("operationCodec", App("Operation.read", N("x")))))));
        var ports = All("q", producer, All("alpha", N("Letter"), All("beta", N("Letter"), All("chi", N("Letter"), All("eta", N("Letter"),
            Arrow(EqF(App("LiveProducer.Current.actualRequest", q), N("false")),
                EqF(App("LiveProducer.Current.step", q, N("alpha"), N("beta")), App("LiveProducer.Current.step", q, N("chi"), N("eta")))))))));
        return All("saved", N("LiveProducer.State"), All("image", N("TransferSnapshot"), All("a", bankType,
            All("c", bankType, All("role", N("Bool"), All("z", N("Runtime"), All("op", N("Operation"),
                Both(App("Function.Injective", N("LiveProducer.Current.code")), charge, preparation, scanner, preserve, writing, fields, acquisition, ports))))))));
    }

    private static Formula MotorRefinement()
    {
        var w = N("w"); var rom = N("rom"); var m = N("m"); var r = N("r");
        var entry = App("motorEntry", w);
        var checkpoint = App("motorCheckpoint", rom, m, N("hm"));
        var paused = All("m", Nat, All("hm", Le(m, w), All("r", Nat, And(
            EqF(App("motorRun", rom, entry, Add(App("motorTime", m), r)),
                App("motorRun", rom, checkpoint, r)),
            EqF(App("motorTrace", rom, entry, Add(App("motorTime", m), r)),
                Seq(Trace(rom, App("copyEntry", w), Mul(D(4), m)), Sp, Plus, Plus, Sp,
                    App("motorTrace", rom, checkpoint, r)))))));
        var tape = EqF(Field(App("motorRun", rom, entry, App("motorTime", w)), "tape"), rom);
        var trace = EqF(App("motorTrace", rom, entry, App("motorTime", w)),
            App("List.ofFn", Fn("i", FinOf(w), App("rom", N("i")))));
        var terminal = With(With(App("motorCheckpoint", rom, w, Seq(N("le"), Underscore, Grp(N("rfl")))),
            "probe", App("Fin.last", w)), "pc", N("MotorPC.halt"));
        var halted = All("n", Nat, EqF(App("motorRun", rom, entry,
            Add(Add(Add(App("motorTime", w), Mul(D(2), w)), D(2)), N("n"))), terminal));
        return All("w", Nat, All("rom", Arrow(FinOf(w), N("Bool")),
            And(paused, And(tape, And(trace, halted)))));
    }

    private static Formula LiteralTransfers()
    {
        var s = N("s"); var q = N("q"); var m = N("m"); var r = N("r"); var slot = N("slot");
        var start = App("literalInstallStart", s);
        Formula RunAt(Formula t) => Iter(N("literalInstallStep"), t, start);
        var state = RunAt(N("ticks")); var motor = Field(state, "installation");
        var invariant = Seq(Exists, Sp, Open, N("m"), Sp, Colon, Sp, Nat, Close, Comma, Sp,
            App("HeadControl", motor, N("m")));
        var noFault = Seq(Field(motor, "pc"), Sp, Neq, Sp, N("MotorPC.fault"));
        var progress = Arrow(Seq(Field(motor, "pc"), Sp, Neq, Sp, N("MotorPC.halt")),
            LtF(App("motorRank", Field(App("literalInstallStep", state), "installation")),
                App("motorRank", motor)));
        var cuts = All("ticks", Nat, And(EqF(Field(state, "base"), Field(s, "base")),
            And(EqF(Field(state, "header"), Field(s, "header")),
            And(EqF(Field(state, "frame"), Field(s, "frame")),
            And(invariant, And(noFault, progress))))));
        var paused = All("m", Nat, All("hm", Le(m, N("programWidth")), All("r", Nat,
            EqF(Field(RunAt(Add(App("motorTime", m), r)), "installation"),
                App("motorRun", N("programTape"),
                    App("motorCheckpoint", N("programTape"), m, N("hm")), r)))));
        var endpoint = RunAt(App("motorTime", N("programWidth")));
        var installed = EqF(Field(Field(endpoint, "installation"), "tape"), N("programTape"));
        var pre = Field(Field(Field(Field(s, "base"), "retained"), "pre"), "fields");
        var op = Field(Field(Field(s, "base"), "retained"), "operation");
        var frames = All("slot", FinOf(D(6)), EqF(
            App("motorTrace", App("literalInstalledFrameROM", endpoint, slot),
                App("motorEntry", N("frameWidth")), App("motorTime", N("frameWidth"))),
            App("bitCode", App("frameCodec", Frame(pre, op, slot)))));
        var block = EqF(App("literalStreamedBlock", pre, op), App("eventBlock", pre, op));
        var charge = All("q", N("TransferSnapshot"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("motorStaticImage"), "length")),
                Field(App("transferCode", q), "length")), N("literalTransferBound")));
        return All("s", N("TransferSnapshot"),
            And(App("Function.Injective", N("transferCode")),
                And(charge, And(cuts, And(paused, And(installed, And(frames, block)))))));
    }

    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, N(x), Sp, Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula TaggedSourceCommit()
    {
        var s = N("s"); var op = N("op"); var slot = N("slot"); var i = N("i");
        var z = Field(Field(Field(s, "base"), "retained"), "actual");
        var stateType = N("LiveProducer.State");
        var prepared = App("LiveProducer.prepared", s, op, slot, i);
        Formula RunAt(Formula t) => App("LiveProducer.run", prepared, D(0), D(0), t);
        var q = N("q");
        var charge = All("q", stateType, LtF(Add(Add(Field(N("programImage"), "length"),
            Field(N("LiveProducer.staticImage"), "length")), Field(App("LiveProducer.code", q), "length")), N("LiveProducer.bound")));
        Formula ports = Arrow(EqF(App("LiveProducer.actualRequest", q), N("false")),
            Arrow(EqF(App("LiveProducer.freshRequest", q), N("false")),
                EqF(App("LiveProducer.step", q, N("a"), N("b")),
                    App("LiveProducer.step", q, N("c"), N("d")))));
        ports = All("d", N("Letter"), ports);
        ports = All("c", N("Letter"), ports);
        ports = All("b", N("Letter"), ports);
        ports = All("a", N("Letter"), ports);
        ports = All("q", stateType, ports);
        Formula Saved(Formula x) => Field(Field(Field(x, "addressed"), "outer"), "base");
        var cuts = All("q", stateType, All("a", N("Letter"), All("b", N("Letter"), All("t", Nat,
            EqF(Field(Saved(App("LiveProducer.run", q, N("a"), N("b"), N("t"))), "retained"),
                Field(Saved(q), "retained"))))));
        var returned = EqF(Field(q, "stage"), N("LiveProducer.Stage.returned"));
        var output = Some("u", Nat, And(Le(N("u"), N("t")), EqF(App("LiveProducer.emitted", RunAt(N("u"))),
            App("some", Seq(App("frameTape", App("eventROM", Field(z, "fields"), op, slot)), Sp, i)))));
        var endpoint = Some("t", Nat, Some("q", stateType, And(EqF(RunAt(N("t")), q),
            And(returned, And(EqF(App("LiveProducer.returnedRuntime", q), App("some", N("d"))),
            And(EqF(App("LiveProducer.returnedOperation", q), App("some", op)), output))))));
        var atN = RunAt(N("n"));
        var rankCuts = All("n", Nat, And(Seq(Field(atN, "stage"), Sp, Neq, Sp, N("LiveProducer.Stage.fault")),
            Arrow(Seq(Field(atN, "stage"), Sp, Neq, Sp, N("LiveProducer.Stage.returned")),
                LtF(App("LiveProducer.rank", App("LiveProducer.step", atN, D(0), D(0))), App("LiveProducer.rank", atN)))));
        var native = All("d", N("Runtime"), Arrow(EqF(App("runtimeStep", z, op), App("some", N("d"))), And(endpoint, rankCuts)));
        var acquired = App("LiveProducer.step", App("LiveProducer.sourceEntry", s, slot, i), N("x"), D(0));
        var sourceReturn = And(returned, And(
            EqF(App("LiveProducer.returnedRuntime", q), App("some", N("d"))),
            EqF(App("LiveProducer.returnedOperation", q), App("some", App("Operation.read", N("x"))))));
        var sourceEndpoint = Some("t", Nat, Some("q", stateType, And(
            EqF(App("LiveProducer.run", acquired, D(0), D(0), N("t")), q), sourceReturn)));
        var source = All("x", N("Letter"), All("d", N("Runtime"), Arrow(
            EqF(App("runtimeStep", z, App("Operation.read", N("x"))), App("some", N("d"))), sourceEndpoint)));
        Formula result = And(native, source);
        result = And(cuts, result);
        result = And(ports, result);
        result = And(charge, result);
        result = And(App("Function.Injective", N("LiveProducer.code")), result);
        result = All("i", FinOf(N("frameWidth")), result);
        result = All("slot", FinOf(D(6)), result);
        result = All("op", N("Operation"), result);
        return All("s", N("TransferSnapshot"), result);
    }

    private static Formula LiteralAddress()
    {
        var s = N("s"); var q = N("q"); var a = N("a"); var i = N("i");
        var entry = App("addressEntry", s, a, i);
        var index = App("addressIndex", a, i);
        Formula RunAt(Formula start, Formula ticks) => App("addressRun", start, ticks);
        var state = RunAt(entry, N("n"));
        var preserved = And(EqF(Field(state, "outer"), s),
            And(EqF(Field(state, "key"), Field(entry, "key")),
            And(EqF(Field(state, "offset"), Field(entry, "offset")), And(
                Seq(Field(Field(state, "control"), "pc"), Sp, Neq, Sp, N("AddressPC.fault")),
                Arrow(Seq(Field(Field(state, "control"), "pc"), Sp, Neq, Sp, N("AddressPC.returned")),
                    LtF(App("addressRank", App("addressStep", state)), App("addressRank", state)))))));
        var cuts = All("a", FinOf(N("frameKeyWidth")), All("i", FinOf(N("frameWidth")),
            All("n", Nat, preserved)));
        var returned = EqF(Field(Field(q, "control"), "pc"), N("AddressPC.returned"));
        var endpoint = Some("ticks", Nat, Some("q", N("AddressState"),
            And(EqF(RunAt(entry, N("ticks")), q), And(returned,
            And(EqF(Field(q, "outer"), s), And(
                EqF(Field(Field(Field(q, "head"), "probe"), "val"), Field(index, "val")),
                And(EqF(Field(Field(q, "control"), "latch"),
                    Seq(Field(Field(s, "installation"), "tape"), Sp, index)),
                    Le(N("ticks"), N("addressTimeBound")))))))));
        var execution = All("a", FinOf(N("frameKeyWidth")), All("i", FinOf(N("frameWidth")), endpoint));
        var installed = Iter(N("literalInstallStep"), App("motorTime", N("programWidth")),
            App("literalInstallStart", s));
        var raw = App("addressEntry", installed, App("frameKey", s, N("slot")), i);
        var pre = Field(Field(Field(Field(s, "base"), "retained"), "pre"), "fields");
        var op = Field(Field(Field(s, "base"), "retained"), "operation");
        var frames = All("slot", FinOf(D(6)), All("i", FinOf(N("frameWidth")),
            Some("ticks", Nat, Some("q", N("AddressState"), And(
                EqF(RunAt(raw, N("ticks")), q), And(returned,
                    EqF(Field(Field(q, "control"), "latch"),
                        Seq(App("frameTape", Frame(pre, op, N("slot"))), Sp, i))))))));
        var charge = All("q", N("AddressState"), LtF(
            Add(Add(Field(N("programImage"), "length"), Field(N("addressStaticImage"), "length")),
                Field(App("addressCode", q), "length")), N("literalAddressBound")));
        return All("s", N("TransferSnapshot"), And(App("Function.Injective", N("addressCode")),
            And(charge, And(cuts, And(execution, frames)))));
    }

    private static Formula SixSlots()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var bound = Le(Field(App("eventBlock", f, op), "length"), D(6));
                var indices = All("i", Nat, All("b", N("Letter"), Seq(
                    App("OriginalEvent.completed", N("i"), N("b")), Sp, InMacro, Sp,
                    App("eventBlock", f, op), Sp, Implies, Sp, LtF(N("i"), D(4)))));
                var blocks = App("List.map", N("original"), App("List.filterMap", N("id"),
                    App("List.ofFn", App("eventROM", f, op))));
                return All("f", N("FiniteFields"), All("op", N("Operation"),
                    And(bound, And(indices, EqF(blocks, App("eventBlock", f, op))))));
    }

    private static Formula StreamedEvents()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var one = All("slot", FinOf(D(6)), And(
                    EqF(Trace(Rom(f, op, slot), N("renderFrame"), Mul(D(4), N("frameWidth"))),
                        App("bitCode", App("frameCodec", Frame(f, op, slot)))),
                    EqF(Field(App("frameRun", f, op, slot, Mul(D(4), N("frameWidth"))), "tape"), Rom(f, op, slot))));
                return All("f", N("FiniteFields"), All("op", N("Operation"),
                    And(one, EqF(Decoded(f, op), App("eventBlock", f, op)))));
    }

    private static Formula ChargedFrames()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(App("installed", s), "frame", N("renderFrame"));

                var charge = All("q", N("RenderSnapshot"), LtF(Add(Field(N("programImage"), "length"),
                    Field(App("snapshot", N("q")), "length")), N("rendererBound")));
                var endpoint = EqF(App("installed", s), Iter(N("installStep"), Mul(D(4), N("programWidth")),
                    With(s, "installation", App("copyEntry", N("programWidth")))));
                var installed = EqF(Field(Field(Iter(N("installStep"), Mul(D(4), N("programWidth")),
                    With(s, "installation", App("copyEntry", N("programWidth")))), "installation"), "tape"), N("programTape"));
                var cp = Cp(Rom(pre, operation, slot), N("m"), N("hm"));
                var equality = EqF(Field(Iter(App("frameStep", slot), Add(Mul(D(4), N("m")), N("r")), entry), "frame"),
                    Run(Rom(pre, operation, slot), cp, N("r")));
                var paused = All("slot", FinOf(D(6)), All("m", Nat,
                    All("hm", Le(N("m"), N("frameWidth")), All("r", Nat, equality))));
                return All("s", N("RenderSnapshot"), And(App("Function.Injective", N("snapshot")),
                    And(charge, And(endpoint, And(installed, And(paused, EqF(InstalledDecoded(s), App("eventBlock", pre, operation))))))));
    }

    private static Formula StreamedHistory()
    {
        var f = N("f"); var op = N("op"); var slot = N("slot");
        var s = N("s"); var pre = Field(Field(Field(s, "retained"), "pre"), "fields");
        var operation = Field(Field(s, "retained"), "operation");
        var entry = With(s, "frame", N("renderFrame"));

                var initial = Field(Field(N("c"), "source"), "finiteFields");
                var final = Field(Field(N("d"), "source"), "finiteFields");
                var blocks = App("streamedBlocks", initial, N("ops"));
                var result = And(EqF(App("fullTranscript", N("c"), N("omega"), N("n")),
                    App("some", Pair(N("ops"), final, blocks))),
                    EqF(App("List.foldl", N("replayBlock"), initial, blocks), final));
                var body = Seq(EqF(App("nativeDrive", N("c"), N("omega"), N("n")),
                    App("some", Pair(N("ops"), N("d"), N("k")))), Sp, Implies, Sp, result);
                body = All("ops", ListOf(N("Operation")), body);
                body = All("k", Nat, body); body = All("n", Nat, body);
                body = All("omega", N("Stream"), body);
                body = All("d", N("AcquiredNativeState"), body);
                return All("c", N("AcquiredNativeState"), body);
    }
}
