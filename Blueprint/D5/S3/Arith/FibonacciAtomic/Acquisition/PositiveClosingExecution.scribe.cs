using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Acquisition;

internal sealed class PositiveClosingExecutionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Acquisition/PositiveClosingExecution.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive reverse closing implements the common-direction policy on one continuous natural-pair source.",
        H("One chronological acquisition trajectory"),
        Blocks(
            Paragraph(Text("The source is any v=(a,b) in Nat squared, including zero. Its original "
                + "operations are R(a,b)=(b,a+b) and G(a,b)=(a+1,b). A chronological Boolean "
                + "word uses true for R and false for G. Run(w,v) is the original runWord, "
                + "q(a,b)=2a+3b, and res(H,v) is coordinatewise reduction in (ZMod H) squared. "
                + "The only informative source event is a paid nondestructive full reply "
                + "gcd(q u,H); action events consume their fixed completion acknowledgement. "
                + "All actions operate on the same source thread in ContinuousAcquisitionTransport.Run.")),
            Definition("matrix", "The public matrix", All("H", N,
                EqOf(C("M", V("H")), C("matrixTwo", D(0), D(1), D(1), D(1)))),
                "M(H) is the matrix with rows (0,1) and (1,1) over ZMod H. Its inverse has "
                + "rows (-1,1) and (1,0), including the singleton ring when H=1."),
            Definition("period", "An effective least matrix period", All("H", N,
                EqOf(L, C("ite", EqOf(V("H"), D(0)), D(1),
                    C("min", C("positiveMatrixPeriods", V("H")))))),
                "L(H)=period(H) is the least positive k with M(H)^k=I for H>0; L(0)=1 "
                + "is an unused public convention. The search is Nat.find with a decidable "
                + "matrix equality. The matrix is a unit. Its finite order is bounded by "
                + "the number of matrix units, which inject into the H^4 matrices. This "
                + "proves termination with 1<=L(H)<=H^4, rather than using a factorial-sized "
                + "closing word. No source query occurs in this public computation."),
            Definition("closing", "Chronological positive closing", All("H", N,
                All("w", C("ListBool"), EqOf(C("close", V("H"), V("w")),
                    C("flatMap", C("closeLetter", V("H")), C("reverse", V("w")))))),
                "closeLetter(H,true) is L(H)-1 individual R calls; closeLetter(H,false) "
                + "is H-1 individual G calls. Subtraction is truncated in these total "
                + "definitions. For H>=1 the exponents are the required nonnegative "
                + "integers. The closing list reverses the original letters before "
                + "expanding them. Thus it cancels the most recent residue action first. "
                + "It is a list of positive original actions, with no inverse-action service."),
            Definition("controller", "A source-blind public controller", All("H", N,
                EqOf(C("P", V("H")), C("Controller", C("code", V("H")),
                    C("initial", V("H")), C("zeroPair")))),
                "Phase(H) has four constructors: stage(s,j,a,y), forward(todo,w,s,j,a,y), "
                + "reading(w,s,j,a,y), and close(todo,s,j,a,y). Here s is Boolean, j is "
                + "a natural counter, a:Joint(H) is the scheduler's public prime-axis "
                + "record, y:ZMod H is the first acquired scalar, and todo,w are finite "
                + "Boolean words. None contains a source coordinate. The direction is "
                + "K(H) when s=false and K(H)+1 when s=true, where K is the existing "
                + "least positive Fibonacci compiler direction. Gamma(H)=graftBound(H) "
                + "is 1+floor((K(H)+2)/2); B(H)=costBound(H) is the maximum of "
                + "factorization(H,p)*(p-1) over the prime divisors p of H."),
            Paragraph(Text("At a nonzero stage counter the code computes c=shift(H,a) "
                + "and w=compile(H,k,c), then enters forward. Each nonempty forward "
                + "list emits its next original action. Its empty list enters reading. "
                + "Reading makes exactly one current gcd call, retains that full reply "
                + "g in the event tape, and enters close(close(H,w),s,j,advanceAll(H,a,g),y). "
                + "Every closing action is completed before the empty closing list "
                + "commits the next stage cut. A completed first stage computes its "
                + "recover value and starts the second stage. A completed second stage "
                + "halts with decode(H,(y,recover(H,a))). For H>1 initialization is "
                + "stage(false,B(H),initialAxis,0). For H=1 it is stage(true,0,initialAxis,0), "
                + "so no source call is made. The fallback is the zero residue pair.")),
            Describe.Lean(DescribeId.Create("positive-closing-residue-run"),
                DeclarationHandle.Create(Prefix + "residue_run"), H("Whole-word residue transport"),
                StatementSource.FromAuthor(All("H", N, All("w", C("ListBool"), All("v", Pair,
                    EqOf(C("res", V("H"), C("Run", V("w"), V("v"))),
                        C("graftRun", C("alpha"), C("mapNot", V("w")), C("res", V("H"), V("v")))))))),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "graftRun is GraftAffineClosure.run with alpha=(1,0). Its Boolean convention "
                    + "is false for replacement and true for graft, so mapNot complements the "
                    + "original chronological word. The equality holds for every natural H and "
                    + "every natural pair, without a positive-modulus premise. It transports the "
                    + "actual original word to its residue action; the installed scratch predictor "
                    + "uses this same transport at every synchronized current cut."))), DescribeRole.Theorem),
            Definition("executionWord", "The action word of this same run", All("H", N,
                All("v", Pair, EqOf(A, C("ite", EqOf(V("H"), D(1)), C("nil"),
                    C("append", C("actions", V("H"), K, C("tape", V("H"), V("v"), C("false"))),
                        C("actions", V("H"), Add(K,D(1)), C("tape", V("H"), V("v"), C("true")))))))),
                "stageData(H,v,s) is the existing rounds(H,compiledReply(H,v,k),B(H),initialAxis), "
                + "with k the public stage direction; tape(H,v,s) is its second component. "
                + "These are mathematical descriptions of a run, not inputs of code. "
                + "actions(H,k,tape) concatenates compile(H,k,c) followed by its positive "
                + "closing list for each tape record (c,g), in order. A(H,v)=executionWord(H,v)."),
            Definition("executionEvents", "The actual full-reply tape", All("H", N,
                All("v", Pair, EqOf(E, C("ite", EqOf(V("H"), D(1)), C("nil"),
                    C("stageEventJoin", V("H"), V("v")))))),
                "E(H,v)=executionEvents(H,v) concatenates the two stage tapes with the "
                + "one intervening compute event. Each test contributes: one compute, "
                + "all forward action events, one compute, one full reply g, every "
                + "closing action event, and one compute. stageEventJoin denotes exactly "
                + "this concatenation of events(H,K,tape(H,v,false)), the intervening "
                + "compute, and events(H,K+1,tape(H,v,true)). Thus no closing call is "
                + "omitted and no cached answer is moved across an action."),
            Definition("tests", "Per-stage actual read counts", All("H", N, All("v", Pair,
                All("s", C("Bool"), EqOf(C("T", V("H"), V("v"), V("s")),
                    C("ite", EqOf(V("H"),D(1)),D(0),C("length",C("tape",V("H"),V("v"),V("s")))))))),
                "T(H,v,s) is zero for H=1 and the length of that actual stage's tape otherwise. "
                + "Write T0=T(H,v,false), T1=T(H,v,true). Each equals B(H) for H>1."),
            Definition("graftSum", "Forward graft counts, one per paid test", All("H", N,
                All("v", Pair, EqOf(C("J",V("H"),V("v")), C("sumForwardGrafts",V("H"),V("v"))))),
                "J(H,v)=graftSum(H,v) sums countG(compile(H,k,c)) over the actual "
                + "triples (k,c,g) of schedule(H,compiledReply(H,v)). It is the sum of "
                + "the individual g_j in the source statement; it does not include "
                + "closing grafts, which multiply this total by H."),
            Definition("graftSuffixes", "Suffix replacement indices", And(
                EqOf(C("suffixes", C("nil")),C("nil")),
                All("w",C("ListBool"),EqOf(C("suffixes",C("consR",V("w"))),C("suffixes",V("w")))),
                All("w",C("ListBool"),EqOf(C("suffixes",C("consG",V("w"))),
                    C("cons",C("countR",V("w")),C("suffixes",V("w")))))),
                "suffixes(w)=graftSuffixes(w) lists, in graft occurrence order, the "
                + "number of R letters strictly after that graft in w. R at the front "
                + "adds no graft index; G at the front contributes countR of its tail. "
                + "suffixAffineSum(w) is the sum, for r in suffixes(w) with multiplicity, "
                + "of iterateR(r,(1,0)); iterateR(r,x) is R iterated r times on x. "
                + "The affine sum therefore follows each actual graft through precisely "
                + "its later replacements, including those in positive closing lists."),
            Describe.Lean(DescribeId.Create("positive-continuous-execution"),
                DeclarationHandle.Create(Prefix + "positive_execution"),
                H("Operational execution, exact counts and every-prefix growth"),
                StatementSource.FromAuthor(Result()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every H>=1 and every natural pair v, the fixed "
                        + "controller has the displayed terminating operational run. The "
                        + "same event tape's complete action projection is A. Its terminal "
                        + "residue equals the entry residue and its earned output is res(H,v). "
                        + "The period is least among all positive matrix return exponents. "
                        + "Every test really executes its compiler word, pays one full "
                        + "current gcd, and completes its closing list before the next test.")),
                    Paragraph(Text("Induction on the remaining rounds proves that every "
                        + "next test starts at the entry residue. Congruence makes its "
                        + "actual reply equal to the existing scheduler's compiled reply "
                        + "on the entry. Positive reverse closing restores that residue "
                        + "and earns the next cut. The existing scheduler then decodes "
                        + "the entry. Its answer function occurs only in this mathematical "
                        + "correspondence; the controller receives only its actual paid replies.")),
                    Paragraph(Text("A word with r replacements and g grafts contributes "
                        + "L(H)r and Hg calls after closing. Summing the actual two tapes "
                        + "gives the exact resource vector. No component is borrowed from "
                        + "a reset run or from the different parity-scan construction. "
                        + "The affine endpoint is indexed by actual suffix counts. On "
                        + "natural pairs R never decreases q and at most doubles it, "
                        + "while G adds exactly two. Induction gives the upper bound "
                        + "and the inequality for every chronological source prefix.")),
                    Paragraph(Text("Read optimality against all continuous competitors, "
                        + "immutable entry storage, a separate synchronized mutable "
                        + "current register, and the installed action/acknowledgement/commit "
                        + "continuation remain separate mathematical interfaces. This "
                        + "execution uses the supplied current gcd service, exclusive "
                        + "serialization, genuine binding and rights, completion of finite "
                        + "local work and sufficient per-run source/controller backing. "
                        + "It does not construct those physical services or derive rights "
                        + "or backing from finite code. All source calls, acknowledgements, "
                        + "local work, tape writes, installation and retention remain charged. "
                        + "In particular the scheduler's bounded public shift search does "
                        + "not establish the original polynomial bit-work or workspace "
                        + "bounds. No resource optimum beyond the separate read problem "
                        + "and no syntax, chronology or whole-memory inverse is asserted.")))))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("positive-closing-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => Call(s,a);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula EqOf(Formula x,Formula y) => Seq(x,Sp,Eq,Sp,y);
    private static Formula LeOf(Formula x,Formula y) => Seq(x,Sp,Le,Sp,y);
    private static Formula Add(Formula x,Formula y) => Par(Seq(x,Plus,y));
    private static Formula Mul(Formula x,Formula y) => Par(Seq(x,Sp,Cdot,Sp,y));
    private static Formula Imp(Formula x,Formula y) => Par(Seq(Par(x),Sp,Implies,Sp,Par(y)));
    private static Formula All(string x,Formula t,Formula b) => Par(Seq(Forall,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,b));
    private static Formula Ex(string x,Formula t,Formula b) => Par(Seq(Exists,Sp,V(x),Sp,InMacro,Sp,t,Comma,Sp,b));
    private static Formula And(params Formula[] fs)
    {
        var r=Par(fs[0]);
        for(var i=1;i<fs.Length;i++) r=Seq(r,Sp,Land,Sp,Par(fs[i]));
        return Par(r);
    }
    private static Formula N => C("Nat");
    private static Formula Pair => C("NatPair");
    private static Formula L => C("L",V("H"));
    private static Formula K => C("K",V("H"));
    private static Formula B => C("B",V("H"));
    private static Formula A => C("A",V("H"),V("v"));
    private static Formula E => C("E",V("H"),V("v"));
    private static Formula R => C("countR",A);
    private static Formula G => C("countG",A);
    private static Formula Out => C("Run",A,V("v"));
    private static Formula Q(Formula v) => C("q",v);
    private static Formula Result()
    {
        var t0=C("T",V("H"),V("v"),C("false"));
        var t1=C("T",V("H"),V("v"),C("true"));
        var least=All("k",N,Imp(And(LeOf(D(1),V("k")),
            EqOf(C("matrixPower",V("H"),V("k")),C("identity"))),LeOf(L,V("k"))));
        var operational=Ex("t",C("Phase",V("H")),C("OperationalRun",C("P",V("H")),V("H"),
            C("initial",V("H")),V("v"),E,V("t"),Out,C("res",V("H"),V("v"))));
        var prefix=All("p",C("ListBool"),All("z",C("ListBool"),Imp(
            EqOf(A,C("append",V("p"),V("z"))),LeOf(Q(C("Run",V("p"),V("v"))),Q(Out)))));
        var endpoint=EqOf(Out,Add(C("iterateR",R,V("v")),C("suffixAffineSum",A)));
        var rbound=Mul(Mul(L,Add(Mul(D(2),K),D(1))),B);
        var gbound=Mul(Mul(Mul(D(2),V("H")),C("Gamma",V("H"))),B);
        var bound=Mul(C("power",D(2),R),Add(Q(V("v")),Mul(D(2),G)));
        return All("H",N,Imp(LeOf(D(1),V("H")),All("v",Pair,And(
            operational,EqOf(C("finalWord",C("nil"),E),A),EqOf(C("res",V("H"),Out),C("res",V("H"),V("v"))),
            LeOf(D(1),L),LeOf(L,C("power",V("H"),D(4))),EqOf(C("matrixPower",V("H"),L),C("identity")),least,
            EqOf(C("paidReads",E),Add(t0,t1)),EqOf(C("paidReads",E),C("ite",EqOf(V("H"),D(1)),D(0),Mul(D(2),B))),
            EqOf(R,Mul(L,Add(Mul(K,t0),Mul(Add(K,D(1)),t1)))),EqOf(G,Mul(V("H"),C("J",V("H"),V("v")))),
            LeOf(R,rbound),LeOf(G,gbound),EqOf(C("length",C("suffixes",A)),G),endpoint,prefix,LeOf(Q(Out),bound),
            Imp(EqOf(V("H"),D(1)),And(EqOf(A,C("nil")),EqOf(E,C("nil"))))))));
    }
}
