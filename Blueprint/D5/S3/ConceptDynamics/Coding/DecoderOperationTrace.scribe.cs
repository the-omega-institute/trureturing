using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class DecoderOperationTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/DecoderOperationTrace.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[.. vars],body);
    private static Formula Ex(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.Exists,[.. vars],body);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1]; for(var j=p.Length-2;j>=0;j--) r=new Formula.Logic(p[j],FormulaLogicOperator.And,r); return r;
    }
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula List(Formula a) => Call("List",a);
    private static Formula Nat => I("Nat");
    private static Formula State(Formula s) => Call("state",s);
    private static Formula Acquired(Formula s) => Call("acquired",s);
    private static Formula Output(Formula s) => Call("output",s);
    private static Formula Add(Formula a,Formula b) => Call("add",a,b);
    private static Formula Append(Formula a,Formula b) => Call("append",a,b);
    private static Formula Frame(Formula c,Formula q,Formula o) => Call("frame",c,q,o);
    private static Formula Initial => Frame(I("initial"),D(0),I("nil"));
    private static Formula RecordType => Fn(Fn(Nat,I("O")),Fn(Fn(Nat,I("I")),I("Prop")));
    private static Formula FrameType => Call("Frame",I("C"),I("O"));
    private static Formula ActionType => Fn(I("C"),Call("Op",I("C"),I("I"),I("O")));
    private static Formula Run(Formula r,Formula s,Formula t) => Call("Run",I("action"),Call("full",r),s,t);
    private static Formula Trace(Formula r,Formula s,Formula t,Formula v) => Call("Trace",I("action"),Call("full",r),s,t,v);
    private static Formula Safety => Call("Safety",I("action"),I("initial"),I("Record"));
    private static Formula Live => Call("Liveness",I("action"),I("initial"),I("Record"),I("InD"));
    private static Formula Replay()
    {
        var s=I("s");var t=I("t");var m=I("m");var w=I("w");var v=I("vertices");
        var suffix=All(Equal(Call("apply",I("r"),Add(Acquired(s),I("j"))),Call("apply",I("otherInput"),Add(I("otherOffset"),I("j")))),B("j",Nat));
        var continuation=All(Imp(suffix,Trace(I("otherInput"),Frame(State(s),I("otherOffset"),I("otherOutput")),
            Frame(State(t),Add(I("otherOffset"),m),Append(I("otherOutput"),w)),v)),
            B("otherInput",Fn(Nat,I("I"))),B("otherOffset",Nat),B("otherOutput",List(I("O"))));
        return Disp(All(Imp(Trace(I("r"),s,t,v),Ex(And(Equal(Acquired(t),Add(Acquired(s),m)),
            Equal(Output(t),Append(Output(s),w)),continuation),B("m",Nat),B("w",List(I("O"))))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),
            B("r",Fn(Nat,I("I"))),B("s",FrameType),B("t",FrameType),B("vertices",List(I("C")))));
    }
    private static Formula Cuts()
    {
        var cut=Call("Cut",I("action"),I("initial"),Call("front",I("r"),I("n")),I("t"));
        return Disp(All(Imp(And(Call("Processing",I("action"),I("initial"),I("Record")),Live,
            Call("Record",I("a"),I("r")),Call("InD",I("a"))),
            Ex(And(cut,Run(I("r"),Initial,I("t"))),B("t",FrameType))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("Record",RecordType),B("InD",Fn(Fn(Nat,I("O")),I("Prop"))),
            B("a",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("n",Nat)));
    }
    private static Formula Addresses()
    {
        var s=I("s");var t=I("otherCut");
        var future=All(Equal(Call("apply",I("r"),Add(Acquired(s),I("j"))),
            Call("apply",I("otherInput"),Add(Acquired(t),I("j")))),B("j",Nat));
        return Disp(All(Imp(And(Safety,Live,Call("Record",I("a"),I("r")),Call("Record",I("b"),I("otherInput")),
            Call("InD",I("a")),Run(I("r"),Initial,s),Run(I("otherInput"),Initial,t),
            Equal(State(s),State(t)),Equal(Output(s),Output(t)),future),Equal(I("a"),I("b"))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("Record",RecordType),B("InD",Fn(Fn(Nat,I("O")),I("Prop"))),
            B("a",Fn(Nat,I("O"))),B("b",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("otherInput",Fn(Nat,I("I"))),
            B("s",FrameType),B("otherCut",FrameType)));
    }
    private static Formula Vertices()
    {
        var code=Call("apply",I("encoding"),I("c"));
        return Disp(All(Imp(And(Call("Record",I("a"),I("r")),Trace(I("r"),Initial,I("t"),I("vertices")),
            Call("le",Acquired(I("t")),I("H")),Call("member",I("c"),I("vertices"))),
            Call("le",Call("toWithTop",Call("length",code)),Call("Peak",I("action"),I("initial"),I("Record"),I("encoding"),I("H")))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("Record",RecordType),B("encoding",Fn(I("C"),List(I("Bool")))),B("H",Nat),
            B("a",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("t",FrameType),B("vertices",List(I("C"))),B("c",I("C"))));
    }

    private static Formula Startup()
    {
        return Disp(All(Imp(And(Run(I("r"),Initial,I("t")),Call("lt",D(0),Acquired(I("t")))),
            Ex(Call("Drain",I("action"),Initial,I("u")),B("u",FrameType))),
            B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
            B("r",Fn(Nat,I("I"))),B("t",FrameType)));
    }
    private static Formula ProcessingFromCompetitors()
    {
        var post=All(Imp(And(Call("Record",I("source"),I("input")),
            Run(I("input"),Initial,Frame(I("c"),I("q"),I("outword"))),Equal(Call("apply",I("action"),I("c")),Call("acquire",I("f"))),
            Equal(Call("apply",I("f"),Call("apply",I("input"),I("q"))),Call("some",Call("pair",I("d"),I("batch"))))),
            Ex(Call("Drain",I("action"),Frame(I("d"),Add(I("q"),D(1)),Append(I("outword"),I("batch"))),I("t")),B("t",FrameType))),
            B("source",Fn(Nat,I("O"))),B("input",Fn(Nat,I("I"))),B("c",I("C")),B("d",I("C")),B("q",Nat),
            B("outword",List(I("O"))),B("batch",List(I("O"))),B("f",Fn(I("I"),Call("Option",Call("Product",I("C"),List(I("O")))))));
        return Disp(All(Imp(And(Safety,Live,Call("Record",I("a"),I("r")),Call("Record",I("beta"),I("otherInput")),
            Call("InD",I("a")),Call("notEqual",Call("apply",I("a"),D(0)),Call("apply",I("beta"),D(0))),post),
            Call("Processing",I("action"),I("initial"),I("Record"))),B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),
            B("action",ActionType),B("initial",I("C")),B("Record",RecordType),B("InD",Fn(Fn(Nat,I("O")),I("Prop"))),
            B("a",Fn(Nat,I("O"))),B("beta",Fn(Nat,I("O"))),B("r",Fn(Nat,I("I"))),B("otherInput",Fn(Nat,I("I")))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite actual operation traces preserve original readable states, emitted batches and acquisition boundaries.",
        H("Primitive decoder operations"),Blocks(
            Describe.Lean(DescribeId.Create("decoder-operation-initial-drain"),DeclarationHandle.Create(Prefix+"initial_drain_of_acquired_run"),
                H("An actual acquired run contains finite startup"),StatementSource.FromAuthor(Startup()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite Run whose acquired count is positive contains a first acquisition. Its preceding retained prefix consists solely of internal operations and ends at the actual acquire state. Transfer to the empty available input gives a Drain from physical initialization. Every prefix vertex is retained; neither global computation bounds nor termination on unreachable states are required."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-processing-from-competitors"),DeclarationHandle.Create(Prefix+"processing_of_safe_live_pair"),
                H("Actual first-label competitors derive startup from the recovery contract"),StatementSource.FromAuthor(ProcessingFromCompetitors()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Safety and Liveness have exactly the all-Record finite-run and positionwise InD meanings displayed above. The two supplied actual records have different first source labels; only the first needs InD liveness. Its live first output cannot occur with zero acquisitions, since the same internal prefix transfers to the competitor and safety would equate their first labels. The acquired run therefore supplies finite startup. Processing then follows from that derived drain and the displayed drains after every actual successful acquisition. Post-acquisition finiteness is not inferred from safety alone. Original complete-readable-state and instruction correspondence remains a separate semantic assessment."))),DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("decoder-operation-trace-replay"),DeclarationHandle.Create(Prefix+"trace_replay"),
                H("Unread suffix replay with independent old output"),StatementSource.FromAuthor(Replay()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Op has internal(next,batch), acquire(input to Option(next,batch)), and stopped. Step has only the two original internal and successful available acquisition rules. Frame consists of the original readable state and external acquired count and output word. action reads only the state. Trace retains its entire state vertex list and every finite edge batch. full(r)(q)=some(r(q)). Replay preserves that vertex list exactly, accumulates the actual acquisition and output increments, and changes neither state identity nor batches. Offset and old-output changes are external bookkeeping. Partial acquisition and unreachable loops remain allowed."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-actual-cut-exists"),DeclarationHandle.Create(Prefix+"actual_cut_exists"),
                H("Position liveness supplies every actual D cut"),StatementSource.FromAuthor(Cuts()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ready means acquire or stopped. A Cut is a finite trace over the available front(r,n), from the physical initial state with acquired zero and empty output, ending Ready at acquired n. No End event is supplied. Processing means a finite internal-only startup drain and a finite internal-only drain after every acquisition actually executed on any Record. It quantifies neither over unreachable states nor impossible acquisitions. Liveness means every position has a finite full-run witness for every Record in InD. Startup gives n=0. Deterministic path comparability and liveness beyond the current finite output force the next acquisition; its actual drain supplies the next cut. This is an explicit operational theorem. Universal correspondence to a prose machine definition, endpoint granularity require independent assessment; finite startup is derived from actual first-label competitors by processing_of_safe_live_pair."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-actual-address-equality"),DeclarationHandle.Create(Prefix+"actual_address_eq"),
                H("Live actual addresses agree after equal-state replay"),StatementSource.FromAuthor(Addresses()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Safety means that on every Record every emitted position in every finite primitive run equals its source address. Liveness is positionwise and restricted to InD. Equal cut states, equal cumulative words and one equal unread suffix imply address equality: choose a liveness witness beyond both the requested position and old output, compare actual paths, replay the continuation, and apply safety on both records. No replay or joint injection is a premise."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-peak-trace-bound"),DeclarationHandle.Create(Prefix+"peak_trace_bound"),
                H("All readable vertices belong to the complete horizon peak"),StatementSource.FromAuthor(Vertices()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ReachThrough(H,c) means some Record has a finite primitive run from physical initialization ending at c with acquired count at most H. Peak is the WithTop Nat supremum of the lengths of the supplied original encodings over all such states. Every trace vertex has its actual prefix run, whose acquired count is no greater than the final count. Initialization, transient workspaces, acquisition states and completed endpoints are included. Infinite peaks are retained. The encoding and its original cost are supplied rather than replaced; no equality with a maximum over chosen cut states is asserted."))),DescribeRole.Theorem))));
}
