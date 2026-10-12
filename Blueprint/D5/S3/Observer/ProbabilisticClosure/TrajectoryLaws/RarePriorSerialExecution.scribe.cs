using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class RarePriorSerialExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorSerialExecution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite scanner flights realize serial adaptive service and native operation returns.",
        H("Serial scanner execution"), Blocks(
            Paragraph(Text("The concrete carrier is the existing finite seven-bit packet and the existing finite service state. Consecutive coordinates of one external fair-bit stream are grouped into packets only for analysis; the service continues to read one bit at a time through its installed bit transition.")),
            Paragraph(Text("The accepted stream is obtained by the generic first-acceptance restart construction. Its first-hit index, unused suffix and packet number are external analysis coordinates. They are not registers, a readable random tape, a new operation, or an uncharged scanner.")),
            Paragraph(Text("The repeated theorem gives the complete iid conditional accepted-packet law and, outside one common null event, identifies every ready-entry execution with the existing reset/bit/compare graph. The finite scanner and adaptive runtime simulation are given below. Full renderer and interpreter charging, COMPLETE membership, the two original compatibility statements and inf-sup risks remain separate obligations.")),
            Definition("vector-packet", "vectorPacket", "Vector to packet", "The seven finite coordinates are packed into the existing seven-bit packet carrier."),
            Definition("packetize", "packetize", "External stream packetization", "The nth packet reads seven consecutive coordinates from one external bit stream."),
            Definition("fresh-bit-law", "freshBitLaw", "External fair-bit law", "The source law is the infinite product of the fair Bernoulli law on the existing bit carrier."),
            Definition("accepted-packets", "acceptedPackets", "Accepted finite packets", "Exactly the existing candidate addresses below 100 are accepted."),
            Theorem("acceptance-positive", "acceptance_positive", "Positive acceptance", "An original positive-mass packet lies in the acceptance set. The serial adaptive runtime law directly uses this supplier for the conditional packet law and measurable repeated draw."),
            Definition("accepted-stream", "acceptedStream", "Accepted packet stream", "Repeated accepted packets are selected by the generic suffix-restart construction."),
            Definition("executed-ready-service", "executedReadyService", "Ready-entry execution", "Each repeated service executes the existing trialRun from its prescribed reset entry until the first accepted packet."),
            Theorem("repeated-fresh-bit-service", "repeated_fresh_bit_service", "Repeated service law", "One external stream has the complete conditional accepted-packet product law, and every ready-entry execution returns the existing threshold result outside one common null event."),
            Paragraph(Text("A Flight contains the existing finite scanner and a finite countdown. The countdown ceiling is k times (k plus one) plus n plus one for a k-key, n-payload table. The entry countdown depends only on the finite query address. Each flight instruction advances the installed instruction graph once and decreases this stored countdown. At zero it reads the scanner result. The invariant holds for every flight, every table and every permitted internal cut, including malformed scanner states.")),
            Paragraph(Text("ServiceMachine has ready, scanning and fault constructors. Every constructor retains its finite Runtime and Service. Scanning additionally retains the complete Flight for the existing 43008-key, 21504-payload service dictionary. A ready bit instruction requests exactly one external bit; reset and comparison supply the deterministic value zero, and the scanner consumes no source data. The input bit is contained in the finite table query. Returned and fault states are absorbing. A launch followed by the stored finite countdown and one return instruction implements the original microStep, for every service state.")),
            Paragraph(Text("Serial trial scheduling executes reset, each required bit and comparison through these scanner flights. A paused bit service consumes precisely its remaining bits. Comparison and returned services consume no bits. Packet lists, first-hit indices, suffixes and service numbers are external execution coordinates; the machine has no packet input port, counter of rejected trials, tape position or readable random archive. Its executable randomness port is the single bitRequest instruction.")),
            Paragraph(Text("Initialization and native operation updates execute the existing initialization and native dictionaries through the same finite flight evaluator. The adaptive threshold is selected from the retained Runtime. Its source control, registers, saturating monitor and mode determine that selection. Pending performs only the unique matching Stop; delivered has no next operation. These cases include all finite control states, the seed prelude, partial original transactions and both fourth phases. The serial recurrence starts from every Runtime, rather than only a selected long history.")),
            Paragraph(Text("One common full-measure event of the original external fair-bit stream supports all services and all adaptive operation-return prefixes. The complete infinite serial runtime law equals the pushforward of the same conditional accepted-packet product law under the finite adaptive recurrence. The proof first establishes the actual scanner-flight invariant and serial trial simulation, then uses both the return and product-law conjuncts of repeated_fresh_bit_service. This is an identity of runtime paths with pending and delivered states, retaining service nonreturn as none on the exceptional source paths.")),
            Paragraph(Text("Explicit mixed-radix codecs include the constructor, retained runtime, service PC, candidate, bit position, scanner registers and countdown. A fixed-width unary encoding is injective on every ready, paused scanning and fault state. The localBound expression is B0 plus machineSize plus one and pays the original complete MicroSnapshot alongside this additional local machine state. It is independent of prior, horizon and rejection count. The finite construction does not require materializing the dictionaries. Initialization and native flights use other table dimensions; this local service bound does not include their stored countdowns or the unified scheduling state. Full renderer and controller-interpreter code accounting, serial service commitment into the unified instruction controller, identity to the original generated marked/full transcript, the two original compatibility statements, COMPLETE membership and original radii/Phi/U remain further obligations.")),
            Describe.Lean(DescribeId.Create("serial-adaptive-execution"),
                DeclarationHandle.Create(Prefix + "serial_adaptive_execution"), H("Serial adaptive execution"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The eight clauses give the flight invariant, one instruction return, port independence at every nonrequesting state, local charge, injective encoding, paused trial simulation, whole adaptive runtime law and common-event operation-return simulation."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorResidentCode")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FreshServiceRestart")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFairBitService")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/RarePriorFullFields"))]));

    private static DocumentBlock.Describe Definition(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Definition);

    private static DocumentBlock.Describe Theorem(string id, string name, string title, string body) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(Statement(name))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(body))), DescribeRole.Theorem);

    private static Formula Statement(string name) => name switch
    {
        "vectorPacket" => All("v", Arrow(App("Fin", D(7)), N("Letter")),
            Equal(App("vectorPacket", N("v")), Seq(Langle, App("v", D(0)), Comma, App("v", D(1)), Comma, App("v", D(2)), Comma,
                App("v", D(3)), Comma, App("v", D(4)), Comma, App("v", D(5)), Comma, App("v", D(6)), Rangle))),
        "packetize" => All("omega", Arrow(Nat, N("Letter")), All("n", Nat,
            Equal(App("packetize", N("omega"), N("n")),
                App("vectorPacket", Seq(Open, N("fun"), Sp, N("i"), Sp, Colon, Sp, App("Fin", D(7)), Sp,
                    Mapsto, Sp, App("omega", Seq(N("n"), Star, D(7), Plus, N("i"), Dot, N("val"))), Close))))),
        "freshBitLaw" => Equal(N("freshBitLaw"),
            App("Measure.infinitePi", Seq(Open, N("fun"), Sp, N("index"), Sp, Colon, Sp, Nat, Sp, Mapsto, Sp,
                App("bernoulliMeasure", D(0), D(1), N("fairParameter")), Close))),
        "acceptedPackets" => Equal(N("acceptedPackets"),
            Seq(OpenBrace, N("p"), Sp, Colon, Sp, N("Packet"), Sp, Vert,
                App("packetEquiv", N("p")), Dot, N("val"), Sp, Lt, Sp, D(1, 0, 0), CloseBrace)),
        "acceptance_positive" => Seq(App("packetLaw", N("acceptedPackets")), Sp, Neq, Sp, D(0)),
        "acceptedStream" => AcceptedStreamFormula(),
        "executedReadyService" => ExecutedReadyServiceFormula(),
        "repeated_fresh_bit_service" =>
            Seq(App("Measure.map", N("acceptedStream"), N("freshBitLaw")), Sp, Eq, Sp,
                App("Measure.infinitePi", Seq(Open, N("fun"), Sp, N("index"), Sp, Colon, Sp, Nat, Sp, Mapsto, Sp,
                    App("ProbabilityTheory.cond", N("packetLaw"), N("acceptedPackets")), Close)), Sp, Land, Sp,
                Open, N("ae"), Sp, N("omega"), Sp, N("under"), Sp, N("freshBitLaw"), Comma, Sp,
                Forall, Sp, Open, N("k"), Sp, Colon, Sp, Nat, Close, Sp, Comma, Sp,
                Forall, Sp, Open, N("t"), Sp, Colon, Sp, N("Threshold"), Close, Sp, Comma, Sp,
                App("executedReadyService", N("t"), N("omega"), N("k")), Sp, Eq, Sp,
                App("some", Seq(Langle, N("t"), Comma, Dot, N("returned"), Comma, D(6), Comma,
                    App("packetEquiv", App("acceptedStream", N("omega"), N("k"))), Comma,
                    OutputBitFormula(), Rangle)), Close),
        _ => N("Unknown")
    };

    private static Formula OutputBitFormula()
    {
        var accepted = App("acceptedStream", N("omega"), N("k"));
        var value = Seq(App("packetEquiv", accepted), Dot, N("val"));
        var threshold = Seq(App("threshold", N("t")), Dot, N("val"));
        return App("if", Seq(value, Sp, Lt, Sp, threshold), D(0), D(1));
    }
    private static Formula AcceptedStreamFormula() =>
        All("omega", Arrow(Nat, N("Letter")), All("n", Nat,
            Equal(App("acceptedStream", N("omega"), N("n")),
                App("FreshServiceRestart.draws", N("acceptedPackets"), N("fallbackPacket"),
                    App("packetize", N("omega")), N("n")))));
    private static Formula ExecutedReadyServiceFormula()
    {
        var suffix = App("FreshServiceRestart.unused", N("acceptedPackets"), N("fallbackPacket"),
            N("k"), App("packetize", N("omega")));
        var first = App("FreshServiceRestart.firstHit", N("acceptedPackets"), suffix);
        var result = Seq(N("match"), Sp, first, Sp, N("with"), Sp,
            Bar, Sp, N("none"), Sp, Rightarrow, Sp, N("none"), Sp,
            Bar, Sp, N("some"), Sp, N("n"), Sp, Rightarrow, Sp,
            App("some", App("trialRun", App("entry", N("t")), suffix,
                App("successor", N("n")))));
        return All("t", N("Threshold"), All("omega", Arrow(Nat, N("Letter")), All("k", Nat,
            Equal(App("executedReadyService", N("t"), N("omega"), N("k")), result))));
    }

    private static Formula Statement() => And(FlightInvariant(), InstructionReturn(), PortLaw(), ChargeLaw(),
        App("Function.Injective", N("machineCode")), TrialLaw(), RuntimeLaw(), CommonReturns());

    private static Formula FlightInvariant()
    {
        var run = App("flightRun", N("table"), N("s"), N("m"));
        var remaining = Field(N("s"), "remaining.val");
        return All("k", Nat, All("n", Nat, All("table", Arrow(App("Fin", N("k")), App("Fin", N("n"))),
            All("s", App("Flight", N("k"), N("n")), All("m", Nat,
                Implies(Rel(N("m"), Leq, remaining), And(
                    Equal(Field(run, "scanner"), App("iterate", App("installedGraphStep", N("table")), N("m"), Field(N("s"), "scanner"))),
                    Equal(Field(run, "remaining.val"), Seq(remaining, Minus, N("m"))))))))));
    }

    private static Formula InstructionReturn()
    {
        var x = App("if", Equal(Field(N("s"), "pc"), N("PC.bit")), N("b"), D(0));
        var f = App("flightEntry", App("bitKeyCodec", Pair(N("s"), N("x"))));
        var law = Equal(App("machineRun", App("machineStep", App("ServiceMachine.ready", N("z"), N("s")), N("b")),
            Seq(Field(N("f"), "remaining.val"), Plus, D(1))),
            App("ServiceMachine.ready", N("z"), App("microStep", N("s"), N("b"))));
        return All("z", N("Runtime"), All("s", N("Service"), All("b", N("Letter"),
            Let("x", N("Letter"), x, Let("f", App("Flight", D(4,3,0,0,8), D(2,1,5,0,4)), f, law)))));
    }

    private static Formula PortLaw() => All("q", N("ServiceMachine"), All("a", N("Letter"), All("b", N("Letter"),
        Implies(Equal(App("bitRequest", N("q")), N("false")),
            Equal(App("machineStep", N("q"), N("a")), App("machineStep", N("q"), N("b")))))));

    private static Formula ChargeLaw()
    {
        var codeLength = Field(App("machineCode", N("q")), "length");
        return All("base", N("MicroSnapshot"), All("q", N("ServiceMachine"), And(
            Equal(codeLength, N("machineSize")),
            Rel(Seq(Field(N("residentCode"), "length"), Plus, Field(App("snapshotCode", N("base")), "length"), Plus, codeLength),
                Lt, N("localBound")))));
    }

    private static Formula TrialLaw() => All("s", N("Service"), All("p", N("Packet"),
        Equal(App("serialTrial", N("s"), N("p")), App("some", App("finishTrial", N("s"), N("p"))))));

    private static Formula RuntimeLaw() => All("z", N("Runtime"),
        Equal(App("Measure.map", App("serialStates", N("z")), N("freshBitLaw")), App("packetRuntimeLaw", N("z"))));

    private static Formula CommonReturns()
    {
        var state = App("packetStates", N("z"), App("acceptedStream", N("omega")), N("k"));
        return Seq(N("ae"), Sp, N("omega"), Sp, N("under"), Sp, N("freshBitLaw"), Comma, Sp,
            All("z", N("Runtime"), And(
                All("n", Nat, Equal(App("serialStates", N("z"), N("omega"), N("n")),
                    App("some", App("packetStates", N("z"), App("acceptedStream", N("omega")), N("n"))))),
                All("k", Nat, Equal(App("serialOperation", state, N("omega"), N("k")),
                    App("packetOperation", state, App("acceptedStream", N("omega"), N("k"))))))));
    }

    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Let(string n, Formula t, Formula v, Formula body) =>
        Seq(N("let"), Sp, N(n), Sp, Colon, Sp, t, Sp, Eq, Sp, v, Sp, N("in"), Sp, body);
    private static Formula Field(Formula v, string name) => Seq(Open, v, Close, Dot, N(name));
    private static Formula Rel(Formula a, Formula r, Formula b) => Seq(a, Sp, r, Sp, b);
    private static Formula Equal(Formula a, Formula b) => Rel(a, Eq, b);
    private static Formula Implies(Formula a, Formula b) => Seq(Open, a, Sp, Rightarrow, Sp, b, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, N(name), Sp, Colon, Sp, type, Close, Sp, Comma, Sp, body);
    private static Formula And(params Formula[] terms)
    {
        var result = new System.Collections.Generic.List<Formula> { Open };
        for (var i = 0; i < terms.Length; i++)
        {
            if (i > 0) result.Add(Seq(Sp, Land, Sp));
            result.Add(terms[i]);
        }
        result.Add(Close);
        return F.Seq(result.ToArray());
    }
    private static Formula App(string name, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { N(name), Sp, Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) terms.Add(Seq(Sp, Comma, Sp));
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
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}
