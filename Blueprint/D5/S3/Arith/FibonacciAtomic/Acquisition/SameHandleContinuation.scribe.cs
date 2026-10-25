using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Acquisition;

internal sealed class SameHandleContinuationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Acquisition/SameHandleContinuation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paid positive closing earns an immutable entry and a synchronized callable current state on the retained source binding.",
        H("Returned arithmetic behavior and serial continued use"),
        Blocks(
            Paragraph(Text("Fix H>=1. Sources are all natural pairs, including zero; true denotes the original "
                + "R(a,b)=(b,a+b), and false denotes G(a,b)=(a+1,b). The only informative source call is the "
                + "paid nondestructive complete reply gcd(2a+3b,H). The local acquisition program is exactly "
                + "PositiveClosingExecution.controller(H). It receives H and its acquired replies; neither "
                + "the source projection nor service tariffs enter its code. Its actual action word w and "
                + "event tape es are executionWord(H,v) and executionEvents(H,v), for the semantic entry v.")),
            Paragraph(Text("A supplied SourceService(T,X) has an arbitrary handle type T and backend-state "
                + "type X. Its value(h,x) is a semantic projection to the actual natural pair at h, not a "
                + "controller port. lawful(h,x) records the supplied lawful authority and adequate provision. "
                + "The relations action(h,b,x,y) and read(h,H,x,g,y) describe successful completed calls. "
                + "For lawful x, an action has value(h,y)=step(b,value(h,x)) and preserves lawfulness. "
                + "A read preserves that value and lawfulness and has g=gcd(q(value(h,x)),H). Calls can "
                + "change backend bookkeeping or finite allocations without adding a numeric reply.")),
            Paragraph(Text("Completion(B,h,H) is the supplied premise at the fixed public modulus H that every admitted next action and "
                + "read on a lawful state completes: for each b,x there is a y with action(h,b,x,y), and "
                + "for each lawful x there are g,y with read(h,H,x,g,y). No read at a different modulus, including zero, is required. This models retained rights, service "
                + "completion and adequate backing under exclusive serial use. It is not constructed from "
                + "a residue, finite program or source size. Dynamically provisioned finite states are "
                + "allowed; no fixed finite capacity for all entries or all future lengths is asserted. "
                + "A concrete backend must justify these premises for its chosen finite run. Unreported "
                + "writers, revoked rights and incomplete commits fall outside this service contract.")),
            Paragraph(Text("ServiceRun uses this very B and h in every action and read constructor. Its "
                + "local transitions are the original controller's compute, action, full-reply and halt "
                + "instructions. Action completion returns only its fixed acknowledgement; only the full "
                + "paid gcd enters a read continuation. There is no allocation, replacement handle, clone, "
                + "reset or source-inverse instruction. Induction through the actual positive-closing Run "
                + "constructs a ServiceRun with the identical event tape and earned output. Every completed backend run has this same tape, output, local terminal state, "
                + "arithmetic endpoint and bill; backend bookkeeping may differ. Its source "
                + "projection has the identical integer endpoint. This correspondence is proved from "
                + "individual supplied service effects and completion, not assumed as a simulation law.")),
            Paragraph(Text("Tariffs has three external natural-valued functions on actual pre-call pairs: "
                + "read, replacement and graft. serviceBill(p,[],v)=0; a compute event contributes nothing; "
                + "an action b contributes its corresponding tariff at v and continues at step(b,v); "
                + "a reply contributes the read tariff at v and continues at v. ServiceRun's work index "
                + "adds precisely these amounts at its actual backend states. Thus serviceBill is the "
                + "same-run sum over paid reads, R and G calls, including all closing letters. Its work "
                + "index is never supplied to code or used to select an action.")),
            Definition("update", "The installed local residue update", All("H", N,
                All("b", C("Bool"), All("c", Residues,
                    EqOf(C("update", V("H"), V("b"), V("c")),
                        C("ite", V("b"), C("R", V("c")), C("addAlpha", V("c"))))))),
                "R(c)=(c.second,c.first+c.second), and addAlpha(c)=c+(1,0), in (ZMod H) squared. "
                + "These are the supplied GraftAffineClosure autonomous updates, with the original alpha graft."),
            Definition("scratch", "Finite hypothetical evaluation", All("H", N,
                All("c", Residues, All("V", Words,
                    EqOf(C("scratch", V("H"), V("c"), V("V")),
                        C("graftRun", C("alpha"), C("mapNot", V("V")), V("c")))))),
                "graftRun is GraftAffineClosure.run with graft vector (1,0). Its Boolean convention "
                + "is opposite to the original runWord, so mapNot complements every letter. Evaluation "
                + "uses only the retained current pair and the supplied finite word. It changes no source."),
            Definition("predict", "Current output and future prediction", All("H", N,
                All("c", Residues, All("V", Words,
                    EqOf(C("predict", V("H"), V("c"), V("V")),
                        C("residueReadout", V("H"), C("scratch", V("H"), V("c"), V("V"))))))),
                "residueReadout(H,z)=gcd((2z.first+3z.second).val,H). The existing representative-independent "
                + "decoder gives the actual current gcd when c is synchronized. The empty word is current "
                + "output; applying this finite computation to every requested prefix gives prefix predictions. "
                + "A hypothetical result is a prediction from acquired memory, not an additional observation."),
            Paragraph(Text("Memory(H) has distinct entry and current residue fields and a phase. A Frame "
                + "contains this local memory and one backend state. The four phases are ready, requested(b), "
                + "completed(b) and acknowledged(b). Only ready exposes the callable reader or predictor. "
                + "MicroStep first records request(b), leaving the backend and registers unchanged. Its "
                + "completion step invokes the actual action(B,h,b) and changes only the backend and phase. "
                + "The acknowledgement event is the same constant event for either action and every source; "
                + "it changes only the phase. Finally commit replaces current by update(H,b,current) and "
                + "returns to ready. Every constructor preserves entry. No read, rebind or source allocation "
                + "is present in this continuation protocol.")),
            Definition("continuationEvents", "The actual four-stage word protocol", All("V", Words,
                EqOf(C("continuationEvents", V("V")), C("flatMapTransactions", V("V")))),
                "flatMapTransactions replaces each chronological letter b with the exact four events "
                + "request(b), complete, acknowledge, commit. ProtocolRun is the empty execution or a "
                + "MicroStep followed by a ProtocolRun. Hence an arbitrary protocol prefix may stop with "
                + "a request pending or after completion, but exposes no new callable cut before commit."),
            Definition("Aligned", "The pending-action invariant", All("T", C("Type"),
                All("X", C("Type"), All("B", C("SourceService", V("T"), V("X")),
                All("h", V("T"), All("H", N, All("f", C("Frame", V("X"), V("H")),
                    EqOf(C("Aligned", V("B"), V("h"), V("H"), V("f")),
                        And(C("lawful", V("B"), V("h"), C("world", V("f"))),
                            C("pendingAgreement", V("B"), V("h"), V("H"), V("f")))))))))),
                "pendingAgreement means current=res(H,value(h,world)) in ready or requested(b), "
                + "and update(H,b,current)=res(H,value(h,world)) in completed(b) or acknowledged(b). "
                + "Each microstep preserves this invariant and entry. In particular the source may have "
                + "advanced while the old local register is still stored, but this intermediate state is "
                + "not callable. Every subsequent ready state has the committed correct current register."),
            Describe.Lean(DescribeId.Create("same-handle-return"), DeclarationHandle.Create(Prefix + "same_handle_return"),
                H("The earned return supports all finite continuations at the read optimum"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the displayed statement v=value(B,h,x), w=executionWord(H,v), "
                        + "es=executionEvents(H,v), e=res(H,v), Q=paidReads(es), and readyFrame(y,e,c) "
                        + "has backend y, immutable entry e, separate current c and phase ready. P(H) is "
                        + "the original positive-closing controller. ServiceRun is indexed by its controller, "
                        + "modulus, initial local/backend states, exact event tape, terminal local/backend "
                        + "states, earned output and external work. ProtocolRun uses the same B,h,H. "
                        + "All displayed conjunctions and implications retain their indicated scopes.")),
                    ContinuationPresentation(),
                    Paragraph(Text("The same result holds for every admitted completed acquisition outcome: "
                        + "any ServiceRun from the given actual x has es as its tape, t as its final local "
                        + "state, e as its earned output, the same arithmetic endpoint and exact serviceBill, "
                        + "and lawful retained authority, with y=x for every outcome at H=1. Continued(B,h,H,v,e,y) names exactly the displayed "
                        + "alignment, all-prefix/callable-cut, finite-word execution and prediction clauses. "
                        + "It is proved for each such backend endpoint y, including outcomes that differ in "
                        + "allocation or bookkeeping. No deterministic-backend choice is required.")),
                    Paragraph(Text("The acquisition output e is actually produced by P(H); it is not "
                        + "installed from a hidden source projection. The supplied D execution restores the "
                        + "entry residue after its last positive closing block. Storing its earned output "
                        + "in two separate fields therefore gives current=res(H,value(h,y)) as well as "
                        + "entry=res(H,v). The supplied whole-word residue transport and decoder prove "
                        + "predict(H,e,W)=terminalGcd(H,W,value(h,y))=terminalGcd(H,W,v) for every W. "
                        + "This returns the callable original R/G behavior, including the empty word, "
                        + "rather than just one reply or a fresh simulated source.")),
                    Paragraph(Text("Induction on MicroStep and ProtocolRun proves entry immutability and "
                        + "the pending-action invariant for every actual finite protocol prefix. At every "
                        + "ready state, all finite predictions agree with continuations of that very actual "
                        + "current source. A second induction constructs a completed protocol for every "
                        + "finite original word V using the actual service at h and only local updates. "
                        + "Every completed actual execution has endpoint V(value(h,y)) and current scratch(H,e,V); each later "
                        + "prediction W equals the entry behavior on V appended to W. The same two "
                        + "inductions apply again at any reachable ready frame. Every actual source letter "
                        + "is paid; the continuation contains no further paid read. All finite choices "
                        + "and externally supplied adaptive word sequences are covered by their actual "
                        + "finite prefixes under the same completion premises.")),
                    Paragraph(Text("Q is zero at H=1 and 2B(H) otherwise. Here B(H) is the existing maximum "
                        + "of h(p-1) for p^h exactly dividing H. The universal lower-bound clause directly "
                        + "uses ContinuousAcquisitionTransport.continuous_acquisition_lower_bound. S is "
                        + "arbitrary local configuration space in Type u for any universe u; the successful competitor "
                        + "may use arbitrary "
                        + "finite adaptive source words and local work and actions after its final read. "
                        + "Only its per-entry termination and common finite worst read budget are required. "
                        + "Entry identification already forces Q<=J, hence the same-handle service attains "
                        + "the original read minimum. At H=1 its event tape is empty and y=x, including "
                        + "backend identity. At every H all zero coordinates remain in the source domain.")),
                    Paragraph(Text("The spatial field at a ready cut is this same current c. Its first "
                        + "two prospective replacement quantities are C*c=(2*c.first+3*c.second, "
                        + "3*c.first+5*c.second), and further quantities follow the supplied Fibonacci "
                        + "step. GraftAffineClosure.result gives observe(R(v))=R(observe(v)), "
                        + "the progression identity, and the inverse (x,y) maps to (5*x-3*y,-3*x+2*y). "
                        + "The full original-alpha behavior quotient identifies precisely this residue "
                        + "pair. These existing correspondences are applied to the acquired synchronized "
                        + "c; they share the same actual cut and do not acquire a second label. Prospective "
                        + "replacement quantities describe arithmetic evolution, not elapsed time or a clock.")),
                    Paragraph(Text("For this identical acquisition word and tape, PositiveClosingExecution "
                        + "also supplies the least 1<=L<=H^4, M^L=I, Q=T0+T1, "
                        + "NR=L*(K*T0+(K+1)*T1), NG=H*J, NR<=L*(2K+1)*B and NG<=2H*Gamma*B. "
                        + "Its exact endpoint is R iterated NR times on v plus the sum of R iterated r "
                        + "times on alpha for every graft's number r of strictly later replacements, "
                        + "with multiplicity. Every actual prefix quantity is bounded by the endpoint, "
                        + "which is at most 2^NR*(q(v)+2NG). The service lift preserves that endpoint, "
                        + "every complete reply and every closing letter; none of these accounts comes "
                        + "from a separately optimized run.")),
                    Paragraph(Text("The numerical workspace O(A+Q*b+b^2) and local-work "
                        + "O(H^4*b^3+(A+Q+1)*b^5), with A=NR+NG and b=ceil(log2(H+1)), remain "
                        + "unproved for this implementation. The actual scheduler uses List.range(H) "
                        + "for public shift search. Its binary refinement proves finite representations "
                        + "and exact decisions, not these bounds. A sequential binary implementation, "
                        + "its finite CRT/prime/Fibonacci tables and short buffer, and a proved cost/space "
                        + "simulation of order search, test selection, compilation, closing, tape writes "
                        + "and decoding are still required under the original bit model. The service sum "
                        + "does not replace these local resource obligations.")),
                    Paragraph(Text("Add actual local bit work, public input/output and fixed-acknowledgement "
                        + "handling, installation of code/data and service blocks, authentic binding and "
                        + "rights, backing provision, source storage/retention and retained records. A "
                        + "global replacement is not one local rewrite or bit operation. Each chosen "
                        + "finite continuation adds its own R/G calls, service tariffs, local input/update/"
                        + "output work and any retained future data; hypothetical evaluation adds local "
                        + "work and no source call. No acquisition bound covers an unbounded future tape. "
                        + "Realizing the current gcd port and these supplied services/rights on a narrower "
                        + "Native, LAB or physical backend remains separate. Arithmetic return recovers "
                        + "neither exact integer source, syntax, chronology, elapsed time nor whole-memory "
                        + "installation. No total-resource optimum or physical inverse is asserted."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/Acquisition/ContinuousAcquisitionTransport")),
         DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Arith/FibonacciAtomic/GraftAffineClosure"))]));

    private static DocumentBlock Definition(string name, string title, Formula statement, string text) =>
        Describe.Lean(DescribeId.Create("same-handle-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))),
            DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => Call(s,a);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula EqOf(Formula x, Formula y) => Seq(x,Sp,Eq,Sp,y);
    private static Formula LeOf(Formula x, Formula y) => Seq(x,Sp,Le,Sp,y);
    private static Formula Imp(Formula x, Formula y) => Par(Seq(Par(x),Sp,Implies,Sp,Par(y)));
    private static Formula All(string x, Formula t, Formula b) => Par(Seq(Forall,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,b));
    private static Formula Ex(string x, Formula t, Formula b) => Par(Seq(Exists,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,b));
    private static Formula And(params Formula[] fs)
    {
        var r=Par(fs[0]);
        for(var i=1;i<fs.Length;i++) r=Seq(r,Sp,Land,Sp,Par(fs[i]));
        return Par(r);
    }
    private static Formula N => C("Nat");
    private static Formula Words => C("ListBool");
    private static Formula Residues => C("ResiduePair",V("H"));
    private static Formula Value(Formula x) => C("value",V("B"),V("h"),x);
    private static Formula Entry => C("res",V("H"),Value(V("x")));
    private static Formula Word => C("executionWord",V("H"),Value(V("x")));
    private static Formula Events => C("executionEvents",V("H"),Value(V("x")));
    private static Formula Reads => C("paidReads",Events);
    private static Formula Ready(Formula x,Formula c) => C("readyFrame",x,Entry,c);
    private static Formula Protocol(Formula a,Formula es,Formula b) => C("ProtocolRun",V("B"),V("h"),V("H"),a,es,b);
    private static Formula Reply(Formula w,Formula x) => C("terminalGcd",V("H"),w,x);
    private static Formula Prediction(Formula c,Formula w) => C("predict",V("H"),c,w);
    private static Formula ContinuedAt(Formula endpoint) =>
        C("Continued",V("B"),V("h"),V("H"),Value(V("x")),Entry,endpoint);

    private static DocumentBlock ContinuationPresentation()
    {
        var endpoint=V("a");
        var future=All("W",Words,And(EqOf(Prediction(Entry,V("W")),Reply(V("W"),Value(endpoint))),
            EqOf(Reply(V("W"),Value(endpoint)),Reply(V("W"),Value(V("x"))))));
        var current=C("current",C("memory",V("f")));
        var backend=Value(C("world",V("f")));
        var cutScratch=C("scratch",V("H"),current,V("V"));
        var cutExecution=All("V",Words,Ex("z",V("X"),And(
            Protocol(V("f"),C("continuationEvents",V("V")),Ready(V("z"),cutScratch)),
            EqOf(Value(V("z")),C("runWord",V("V"),backend)),
            EqOf(cutScratch,C("res",V("H"),Value(V("z")))),
            All("W",Words,EqOf(Prediction(cutScratch,V("W")),Reply(C("append",V("V"),V("W")),backend))))));
        var cuts=All("r",C("ListSignal"),All("f",C("Frame",V("X"),V("H")),
            Imp(Protocol(Ready(endpoint,Entry),V("r"),V("f")),And(
                EqOf(C("entry",C("memory",V("f"))),Entry),C("Aligned",V("B"),V("h"),V("H"),V("f")),
                Imp(EqOf(C("phase",C("memory",V("f"))),C("ready")),And(
                    EqOf(current,C("res",V("H"),backend)),All("W",Words,EqOf(Prediction(current,V("W")),Reply(V("W"),backend))),cutExecution))))));
        var scratch=C("scratch",V("H"),Entry,V("V"));
        var continuations=All("V",Words,Ex("z",V("X"),And(
            Protocol(Ready(endpoint,Entry),C("continuationEvents",V("V")),Ready(V("z"),scratch)),
            EqOf(Value(V("z")),C("runWord",V("V"),Value(endpoint))),EqOf(scratch,C("res",V("H"),Value(V("z")))),
            All("W",Words,EqOf(Prediction(scratch,V("W")),Reply(C("append",V("V"),V("W")),Value(V("x"))))))));
        var allWords=All("V",Words,All("f",C("Frame",V("X"),V("H")),
            Imp(Protocol(Ready(endpoint,Entry),C("continuationEvents",V("V")),V("f")),And(
                EqOf(C("phase",C("memory",V("f"))),C("ready")),
                EqOf(current,C("scratch",V("H"),Entry,V("V"))),
                EqOf(backend,C("runWord",V("V"),Value(endpoint))),
                All("W",Words,EqOf(Prediction(current,V("W")),
                    Reply(C("append",V("V"),V("W")),Value(V("x")))))))));
        return new DocumentBlock.Section(H("The complete continuation contract at each backend endpoint"), Blocks(
            Paragraph(Text("For the same fixed T,X,H,B,h,x and the abbreviations v,e above, let a be any "
                + "backend endpoint in X. Continued(B,h,H,v,e,a) means exactly the conjunction of the "
                + "following five formulas, in order. The theorem asserts this entire conjunction at y "
                + "and at every admitted completed acquisition endpoint y2. The formulas share these "
                + "fixed parameters; each displayed quantifier and implication keeps its full scope. "
                + "This is the existing Lean definition Continued with start=readyFrame(a,e,e).")),
            Paragraph(Text("The installed returned cut is aligned:")),
            new DocumentBlock.DisplayFormula(C("Aligned",V("B"),V("h"),V("H"),Ready(endpoint,Entry))),
            Paragraph(Text("Every actual finite protocol prefix preserves entry and alignment; each "
                + "reachable ready frame has its synchronized reader and every further finite execution:")),
            new DocumentBlock.DisplayFormula(cuts),
            Paragraph(Text("Every finite original word has a completed actual execution from the returned cut, "
                + "with its exact source endpoint, synchronized current and all later predictions:")),
            new DocumentBlock.DisplayFormula(continuations),
            Paragraph(Text("Every completed actual execution of such a word has the displayed ready phase, "
                + "current, arithmetic endpoint and all later predictions:")),
            new DocumentBlock.DisplayFormula(allWords),
            Paragraph(Text("Every finite future prediction at the returned cut agrees with both the actual "
                + "returned source and the entry source, including the empty word:")),
            new DocumentBlock.DisplayFormula(future)));
    }

    private static Formula Result()
    {
        var competitor=All("S",C("Type"),All("P",C("Controller",V("S"),Residues),All("J",N,
            Imp(All("z",C("NatPair"),Ex("r",C("ListEvent"),Ex("s",V("S"),Ex("u",C("NatPair"),And(
                C("Run",V("P"),V("H"),C("initial",V("P")),V("z"),V("r"),V("s"),V("u"),C("res",V("H"),V("z"))),
                LeOf(C("paidReads",V("r")),V("J"))))))),LeOf(Reads,V("J"))))));
        var allAcquisitions=All("rs",C("ListEvent"),All("t2",C("AcquisitionPhase",V("H")),
            All("y2",V("X"),All("l2",Residues,All("n2",N,
                Imp(C("ServiceRun",V("B"),V("h"),V("p"),C("P",V("H")),V("H"),
                    C("initial",C("P",V("H"))),V("x"),V("rs"),V("t2"),V("y2"),V("l2"),V("n2")),
                    And(EqOf(V("rs"),Events),EqOf(V("t2"),V("t")),EqOf(V("l2"),Entry),
                        EqOf(Value(V("y2")),C("runWord",Word,Value(V("x")))),
                        C("lawful",V("B"),V("h"),V("y2")),
                        EqOf(V("n2"),C("serviceBill",V("p"),Events,Value(V("x")))),
                        Imp(EqOf(V("H"),D(1)),EqOf(V("y2"),V("x"))),
                        ContinuedAt(V("y2")))))))));
        var body=Ex("t",C("AcquisitionPhase",V("H")),Ex("y",V("X"),And(
            C("ServiceRun",V("B"),V("h"),V("p"),C("P",V("H")),V("H"),C("initial",C("P",V("H"))),
                V("x"),Events,V("t"),V("y"),Entry,C("serviceBill",V("p"),Events,Value(V("x")))),
            EqOf(Value(V("y")),C("runWord",Word,Value(V("x")))),C("lawful",V("B"),V("h"),V("y")),
            EqOf(Reads,C("ite",EqOf(V("H"),D(1)),D(0),C("twice",C("costBound",V("H"))))),
            Imp(EqOf(V("H"),D(1)),EqOf(V("y"),V("x"))),competitor,
            ContinuedAt(V("y")),allAcquisitions)));
        return All("T",C("Type"),All("X",C("Type"),All("H",N,Imp(LeOf(D(1),V("H")),
            All("B",C("SourceService",V("T"),V("X")),All("h",V("T"),Imp(C("Completion",V("B"),V("h"),V("H")),
                All("p",C("Tariffs"),All("x",V("X"),Imp(C("lawful",V("B"),V("h"),V("x")),body))))))))));
    }
}
