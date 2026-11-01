using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Acquisition;

internal sealed class OnlineCommonOriginalArchiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Acquisition/OnlineCommonOriginalArchive.";
    private static Formula Words => C("ListBool");
    private static Formula E(Formula b) => C("envelope", b);
    private static Formula Val(Formula x) => C("value", V("B"), V("h"), x);
    private static Formula Res(Formula d, Formula x) => C("residueSource", d, x);
    private static Formula All(string x, Formula t, Formula f) => Par(Seq(Forall,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,f));
    private static Formula Ex(string x, Formula t, Formula f) => Par(Seq(Exists,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,f));
    private static Formula Eq(Formula x, Formula y) => Seq(x,Sp,F.Eq,Sp,y);
    private static Formula Imp(Formula x, Formula y) => Par(Seq(Par(x),Sp,Implies,Sp,Par(y)));
    private static Formula And(params Formula[] xs)
    {
        var r=Par(xs[0]);
        for(var i=1;i<xs.Length;i++) r=Seq(r,Sp,Land,Sp,Par(xs[i]));
        return Par(r);
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => Call(s,a);
    private static Formula N => C("Nat");
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula LeOf(Formula x,Formula y) => Seq(x,Sp,Le,Sp,y);
    private static Formula LtOf(Formula x,Formula y) => Seq(x,Sp,Lt,Sp,y);
    private static DocumentBlock Definition(string name,string title,Formula statement,string text) =>
        Describe.Lean(DescribeId.Create("online-"+name.ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),H(title),
            StatementSource.FromAuthor(statement),AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Definition);
    private static DocumentBlock Theorem(Formula statement,string text) =>
        Describe.Lean(DescribeId.Create("complete-online-archive"),DeclarationHandle.Create(Prefix+"complete_online_archive"),
            H("All completed finite prefixes of one changing source"),StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula A => V("a");
    private static Formula X => V("x");
    private static Formula Precision => C("precision", A);
    private static Formula Modulus => E(Precision);
    private static Formula Joint => C("jointField", A);
    private static Formula M => C("costBound", Joint);
    private static Formula Tape => C("tape", A);
    private static Formula Sound => C("Sound", V("B"), V("h"), V("x0"), A, X);
    private static Formula Service => C("ArchiveService", V("B"), V("h"), V("x0"), A, X);
    private static Formula Online(Formula inputs, Formula a, Formula x) =>
        C("OnlineRun", V("B"), V("h"), V("p"), C("initial"), V("x0"), inputs, a, x);
    private static Formula Reduce(Formula d, Formula c) => C("reduce", d, Modulus, V("div"), c);
    private static Formula SourceScope(Formula body)
    {
        body=All("x0",V("World"),body);
        body=All("h",V("Handle"),body);
        body=All("B",C("SourceService",V("Handle"),V("World")),body);
        body=All("World",C("Type"),body);
        return All("Handle",C("Type"),body);
    }
    private static Formula ArchiveScope(Formula body) =>
        SourceScope(All("a",C("Memory"),All("x",V("World"),body)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Successively acquired precisions label one original source and every authentic retained cut, with a cumulative bound on actual paid reads.",
        H("An online common-original arithmetic archive"),
        Blocks(
            Paragraph(Text("The source is one natural pair v0, including zero, at one opaque retained binding h. "
                + "The original actions are R(a,b)=(b,a+b) and G(a,b)=(a+1,b); true denotes R. "
                + "SourceService gives their actual completed effects, fixed acknowledgements and a nondestructive "
                + "paid current reply gcd(2a+3b,H). Its value map is a semantic projection and is never a program input. "
                + "VariableCompletion(B,h) requires completion at every positive public modulus used by the program. "
                + "This includes its envelopes, not just the requested moduli. Lawful rights, exclusive serialization, "
                + "absence of side channels and adequate finite material for each chosen finite run remain supplied premises.")),
            Definition("envelope", "One public integer covers a budget", Seq(All("b", N,
                Eq(E(V("b")), Seq(
                    new Formula.Subscript(Prod, Seq(V("p"), Sp, InMacro, Sp, N, Comma, Sp,
                        C("Prime", V("p")), Sp, Land, Sp, LeOf(V("p"), Seq(V("b"), Plus, D(1))))), Sp,
                    new Formula.Power(V("p"), new Formula.Floor(
                        new Formula.Fraction(V("b"), Seq(V("p"), Minus, D(1)))))))),
                Comma, Sp, Eq(E(D(0)), D(1))),
                "primes(b) is the prime filter of range(b+2), and envelope(b) is the product of p^(b/(p-1)) over it. "
                + "Division is natural integer division. Thus envelope(0)=1. For every positive H, H divides envelope(b) "
                + "exactly when costBound(H)<=b; costBound(envelope(b))=b. Increasing b increases the envelope by divisibility."),
            Definition("budget", "Least covering power of two", All("m", N,
                Eq(C("budget", V("m")), C("ite", Eq(V("m"), D(0)), D(0),
                    C("pow", D(2), C("clog", D(2), V("m")))))),
                "Nat.clog is the integer ceiling logarithm. For m>0 this gives m<=budget(m)<2m, "
                + "and budget(m)<=2^k for every integer k with m<=2^k. It uses integer computation."),
            Paragraph(Text("Memory has precision, joint, requests, tape, original and current fields. The two residue "
                + "registers belong to (ZMod envelope(precision)) squared. initial has precision 0, joint 1, empty "
                + "requests and tape, and the singleton zero registers. Every actual completed action and its fixed "
                + "acknowledgement is recorded as an action event. Each paid reply records both its modulus and value. "
                + "Compute events are local intervals with no source reply. letters removes computes and replies, "
                + "reads counts every reply occurrence, and cutWord(tape,t) takes the first t actual source letters. "
                + "TapeRun is generated by the actual service calls on this same binding. Every t up to the letter "
                + "count consequently names an actual past cut, including acquisition and closing cuts.")),
            Paragraph(Text("A delivered positive request H is covered when costBound(H)<=precision. A covered request "
                + "updates the request list and its lcm with no source call. On a miss the new precision is "
                + "budget(costBound(H)); the program runs PositiveClosingExecution.controller at its exact envelope. "
                + "RequestRun requires that controller's actual ServiceRun, starting at the current world, including "
                + "all closing letters. Only after it halts does install append the stamped tape, store the earned "
                + "stage-entry label d as current, and set original=rewind(E,oldLetters,d). Rewind reverses recorded "
                + "letters locally: R is inverted by (x,y)->(y-x,x), and G by (x,y)->(x-1,y), in the residue ring. "
                + "It calls no source inverse and inspects no hidden integer. The fixed acquisition code takes "
                + "only public arithmetic and replies acquired on its actual execution.")),
            Paragraph(Text("A continuation input supplies a finite chronological word. ContinueRun uses the existing "
                + "request, actual completion, fixed acknowledgement and local commit protocol, with original "
                + "immutable and current updated by scratch. advanceMemory appends its actual action letters. "
                + "There is no read instruction in this protocol. OnlineRun sequentially composes these request "
                + "and continuation calls, admitting the next input only at their completed cuts. Its rules "
                + "consult only that next delivered input. Quantification over every finite input list therefore "
                + "includes every realized finite adaptive history, repeated requests and empty continuations, "
                + "without any promise of future precision or source-independent choices by the environment.")),
            Definition("Sound", "One-source archive and actual payment invariant", SoundFormula(),
                "joint(requests) folds lcm from 1; maximum(requests) folds max of costBound from 0. "
                + "TapeRun uses actual service relations, not a supplied archive certificate. The lcm is positive, "
                + "and its cost equals the maximum of the delivered request costs. All paid reads are counted "
                + "with multiplicity. The invariant has no bound on source letters, total work or storage."),
            Definition("Compatible", "A completed request preserves the old archive", Compatibility(),
                "The divisor d reduces residues from the new envelope to the old one. The current-register equality concerns "
                + "current at the upgrade entry, not current at the original cut. Old intervening continuations "
                + "are preserved. Past labels agree at every common authentic cut."),
            Definition("ArchiveService", "Covered arithmetic and synchronized continued use", ServiceFormula(),
                "past(a,D,div,t) is scratch(D,reduce(D,E,div,original),cutWord(tape,t)). "
                + "CoveredServices is expanded below. ContinuedService quantifies every supplied finite word w "
                + "and an actual endpoint y with ContinueRun, unchanged paid-read count and original register, "
                + "and synchronized current at y. LeastDyadicBenchmark gives precision=2^k for some k, "
                + "m<=precision<2m, minimality among covering powers of two, and 8m=4Qret(joint), when m is nonzero. "
                + "The final clause gives completion of every next delivered request from this actual completed "
                + "memory and world. Any two actual executions of that request from this same "
                + "memory and world return identical accessible memory and the same actual arithmetic endpoint. "
                + "The covered/miss guards are disjoint, and the supplier fixes the acquired tape and output."),
            new DocumentBlock.DisplayFormula(ArchiveScope(CoveredServices())),
            Paragraph(Text("In CoveredServices, z is the semantic actual world at the named past cut; no handle to it "
                + "is returned. Its spatial label is past(a,D,div,t). For every word W, the installed predictor "
                + "evaluates the complete arithmetic boundary there without reading the source. For every j, "
                + "quantity(scratch(D,past,replicate(j,true))) equals the actual prospective replacement quantity "
                + "at that cut reduced modulo D. This is a prospective progression, not elapsed time or a new "
                + "oracle. Predictions for unexecuted words are not observations or actual executions from the past.")),
            Definition("UpgradeRecovery", "Transport at every newly chosen positive precision", UpgradeFormula(),
                "For any authentic old tape ending at x, an actual completed acquisition at E>1 earns "
                + "d=residue(E,value(h,x)), returns the actual current source to d modulo E, and installs "
                + "Continued(B,h,E,value(h,x),d,y) at its actual endpoint y. Its paid reads are 2costBound(E). "
                + "The local inverse of the old recorded word computes original=residue(E,v0). The concatenated "
                + "actual tape includes every acquisition and closing action. At every genuine cut it computes "
                + "the spatial label, full finite-word boundary and prospective replacement quantities. For "
                + "every positive divisor D of E, reduction gives the original residue modulo D, the upgrade-entry "
                + "current modulo D, and every common past-cut residue. These equal any previously earned labels "
                + "of that same source and cuts. The return concerns the upgrade entry and preserves earlier "
                + "continuations; it neither rewinds the actual integer nor recovers a past source handle."),
            Theorem(Result(),
                "Induction over actual request and continuation segments establishes Sound. At a miss, the "
                + "invariant consumes the arbitrary-modulus UpgradeRecovery theorem at the newly chosen envelope. "
                + "Physical acquisition returns the current source modulo that envelope. Local rewind recovers the "
                + "same v0 from its authentic old prefix. The executed full tape then labels every actual past "
                + "cut. A miss jumps to a larger dyadic budget; except at the first upgrade it is at least twice "
                + "the preceding positive budget. Each stage pays exactly twice its envelope cost. Induction "
                + "therefore bounds the cumulative actual paid reads by 4b-2. The least covering dyadic gives "
                + "4b-2<8m=4Qret(joint). At m=0 the count is zero. The physical run is constructed from the "
                + "supplied service completion and fixed-modulus execution, never postulated as a certificate."),
            Paragraph(Text("The comparison is with the fixed-modulus one-shot worst read budget at the joint lcm. "
                + "It is not an optimum for variable-modulus policies. Source actions, including every closing "
                + "letter, retain their actual counts and source-service tariffs; local computation, recording, "
                + "input/output, acknowledgements, installation, rights, backing and retention are separately "
                + "charged. There is no claim of total-work, action or storage competitiveness, nor a fixed "
                + "capacity for an infinite archive. Arithmetic labels do not recover source syntax, exact "
                + "unbounded coordinates, elapsed time, rights or the rest of the memory installation."))
        )));

    private static Formula SoundFormula() => ArchiveScope(Eq(Sound, And(
        C("TapeRun", V("B"), V("h"), V("x0"), Tape, X), C("lawful", V("B"), V("h"), X),
        LtOf(D(0), Joint), Eq(Joint, C("joint", C("requests", A))),
        Eq(M, C("maximum", C("requests", A))), Eq(Precision, C("budget", M)),
        Eq(C("original", A), Res(Modulus, Val(V("x0")))), Eq(C("current", A), Res(Modulus, Val(X))),
        All("H", N, Imp(C("mem", V("H"), C("requests", A)),
            And(LtOf(D(0), V("H")), C("dvd", V("H"), Modulus)))),
        C("ite", Eq(M, D(0)), Eq(C("reads", Tape), D(0)),
            And(LeOf(C("reads", Tape), C("sub", C("mul", D(4), Precision), D(2))),
                LtOf(C("sub", C("mul", D(4), Precision), D(2)), C("mul", D(8), M)))))));

    private static Formula Compatibility()
    {
        var next=E(C("precision",V("b")));
        var word=C("cutWord",Tape,V("t"));
        var pastEq=Eq(C("reduce",Modulus,next,V("d"),C("scratch",next,C("original",V("b")),word)),
            C("scratch",Modulus,C("original",A),word));
        var body=And(
            Eq(C("reduce",Modulus,next,V("d"),C("original",V("b"))),C("original",A)),
            Eq(C("reduce",Modulus,next,V("d"),C("current",V("b"))),C("current",A)),
            All("t",N,Imp(LeOf(V("t"),C("length",C("letters",Tape))),pastEq)));
        return All("a",C("Memory"),All("b",C("Memory"),Eq(C("Compatible",A,V("b")),
            Ex("d",C("Divides",Modulus,next),body))));
    }

    private static Formula ServiceFormula()
    {
        var next=C("advanceMemory",A,V("w"));
        var continuation=All("w",Words,Ex("y",V("World"),And(
            C("ContinueRun",V("B"),V("h"),A,V("w"),X,V("y")),
            Eq(C("reads",C("tape",next)),C("reads",Tape)),Eq(C("original",next),C("original",A)),
            Eq(C("current",next),Res(Modulus,Val(V("y")))))));
        var benchmark=And(Ex("k",N,Eq(Precision,C("pow",D(2),V("k")))),
            LeOf(M,Precision),LtOf(Precision,C("mul",D(2),M)),
            All("k",N,Imp(LeOf(M,C("pow",D(2),V("k"))),LeOf(Precision,C("pow",D(2),V("k"))))),
            Eq(C("mul",D(8),M),C("mul",D(4),C("ite",Eq(Joint,D(1)),D(0),C("mul",D(2),M)))));
        var deterministic=Imp(And(
            C("RequestRun",V("B"),V("h"),V("p0"),A,V("H"),X,V("b"),V("y")),
            C("RequestRun",V("B"),V("h"),V("p0"),A,V("H"),X,V("c"),V("z"))),
            And(Eq(V("b"),V("c")),Eq(Val(V("y")),Val(V("z")))));
        deterministic=All("z",V("World"),deterministic);
        deterministic=All("c",C("Memory"),deterministic);
        deterministic=All("y",V("World"),deterministic);
        deterministic=All("b",C("Memory"),deterministic);
        var completion=Ex("b",C("Memory"),Ex("y",V("World"),
            C("RequestRun",V("B"),V("h"),V("p0"),A,V("H"),X,V("b"),V("y"))));
        deterministic=And(completion,deterministic);
        deterministic=All("H",N,deterministic);
        deterministic=All("p0",C("Tariffs"),deterministic);
        return ArchiveScope(Eq(Service,And(CoveredServices(),continuation,Imp(C("nonzero",M),benchmark),deterministic)));
    }

    private static Formula CoveredServices()
    {
        var d=V("D"); var label=C("past",A,d,V("div"),V("t"));
        var word=C("cutWord",Tape,V("t")); var z=Val(V("z"));
        var predictions=All("W",Words,Eq(C("predict",d,label,V("W")),C("terminalGcd",d,V("W"),z)));
        var replacements=C("replicate",V("j"),C("true"));
        var quantities=All("j",N,Eq(C("quantity",C("scratch",d,label,replacements)),
            C("natCast",d,C("quantity",C("runWord",replacements,z)))));
        var pastBody=And(C("lawful",V("B"),V("h"),V("z")),Eq(z,C("runWord",word,Val(V("x0")))),
            Eq(label,Res(d,z)),predictions,quantities);
        var cuts=All("t",N,Imp(LeOf(V("t"),C("length",C("letters",Tape))),Ex("z",V("World"),pastBody)));
        var body=And(Eq(Reduce(d,C("original",A)),Res(d,Val(V("x0")))),
            Eq(Reduce(d,C("current",A)),Res(d,Val(X))),
            All("W",Words,Eq(C("predict",d,Reduce(d,C("current",A)),V("W")),C("terminalGcd",d,V("W"),Val(X)))),cuts);
        return All("D",N,Imp(LtOf(D(0),d),All("div",C("Divides",d,Modulus),body)));
    }

    private static Formula UpgradeFormula()
    {
        var old=V("old"); var e=V("E"); var d=V("d");
        var tape=C("append",old,C("mapStamp",e,V("es")));
        var orig=C("rewind",e,C("letters",old),d);
        var label=C("scratch",V("D"),C("reduce",V("D"),e,V("div"),orig),C("cutWord",tape,V("t")));
        var past=And(C("lawful",V("B"),V("h"),V("z")),
            Eq(Val(V("z")),C("runWord",C("cutWord",tape,V("t")),Val(V("x0")))),
            Eq(label,Res(V("D"),Val(V("z")))),
            All("W",Words,Eq(C("predict",V("D"),label,V("W")),C("terminalGcd",V("D"),V("W"),Val(V("z"))))),
            All("j",N,Eq(C("quantity",C("scratch",V("D"),label,C("replicate",V("j"),C("true")))),
                C("natCast",V("D"),C("quantity",C("runWord",C("replicate",V("j"),C("true")),Val(V("z"))))))));
        var divisors=All("D",N,Imp(LtOf(D(0),V("D")),All("div",C("Divides",V("D"),e),And(
            Eq(C("reduce",V("D"),e,V("div"),orig),Res(V("D"),Val(V("x0")))),
            Eq(C("reduce",V("D"),e,V("div"),d),Res(V("D"),Val(X))),
            All("t",N,Imp(LeOf(V("t"),C("length",C("letters",tape))),Ex("z",V("World"),past)))))));
        var body=Eq(C("UpgradeRecovery",V("B"),V("h"),V("x0"),old,X,e,V("es"),d,V("y")),And(
            C("TapeRun",V("B"),V("h"),V("x0"),tape,V("y")),Eq(orig,Res(e,Val(V("x0")))),
            Eq(d,Res(e,Val(X))),Eq(d,Res(e,Val(V("y")))),
            Eq(C("paidReads",V("es")),C("ite",Eq(e,D(1)),D(0),C("mul",D(2),C("costBound",e)))),
            C("Continued",V("B"),V("h"),e,Val(X),d,V("y")),divisors));
        body=All("y",V("World"),body);
        body=All("d",C("ResiduePair",e),body);
        body=All("es",C("ListEvent"),body);
        body=All("E",N,body);
        body=All("x",V("World"),body);
        return SourceScope(All("old",C("ListTapeEvent"),body));
    }

    private static Formula UpgradeClaim()
    {
        var e=V("E"); var controller=C("controller",e);
        var run=C("ServiceRun",V("B"),V("h"),V("p"),controller,e,C("initialState",controller),
            X,V("es"),V("t"),V("y"),V("d"),V("n"));
        var body=Imp(run,C("UpgradeRecovery",V("B"),V("h"),V("x0"),V("old"),X,e,V("es"),V("d"),V("y")));
        body=All("n",N,body);
        body=All("d",C("ResiduePair",e),body);
        body=All("y",V("World"),body);
        body=All("t",C("AcquisitionPhase",e),body);
        body=All("es",C("ListEvent"),body);
        body=Imp(C("TapeRun",V("B"),V("h"),V("x0"),V("old"),X),body);
        body=Imp(LtOf(D(1),e),body);
        body=All("E",N,body);
        body=All("x",V("World"),body);
        return All("old",C("ListTapeEvent"),body);
    }

    private static Formula Result()
    {
        var existence=All("inputs",C("ListInput"),Ex("a",C("Memory"),Ex("x",V("World"),Online(V("inputs"),A,X))));
        var safety=All("inputs",C("ListInput"),All("a",C("Memory"),All("x",V("World"),
            Imp(Online(V("inputs"),A,X),And(Sound,Service)))));
        var request=C("RequestRun",V("B"),V("h"),V("p"),A,V("H"),X,V("b"),V("y"));
        var upgrade=All("b",C("Memory"),All("y",V("World"),Imp(request,C("Compatible",A,V("b")))));
        var compatible=All("inputs",C("ListInput"),All("a",C("Memory"),All("x",V("World"),All("H",N,
            Imp(LtOf(D(0),V("H")),Imp(Online(V("inputs"),A,X),upgrade))))));
        var transport=UpgradeClaim();
        var body=And(existence,safety,compatible,transport);
        body=Imp(C("lawful",V("B"),V("h"),V("x0")),body);
        body=All("x0",V("World"),body);
        body=All("p",C("Tariffs"),body);
        body=Imp(C("VariableCompletion",V("B"),V("h")),body);
        body=All("h",V("Handle"),body);
        body=All("B",C("SourceService",V("Handle"),V("World")),body);
        body=All("World",C("Type"),body);
        return All("Handle",C("Type"),body);
    }
}
