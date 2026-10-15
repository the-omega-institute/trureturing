using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class DecoderReplayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/DecoderReplay.";
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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Unread suffix replay preserves primitive traces and identifies safe live source addresses.",
        H("Primitive decoder replay and source addresses"),Blocks(
            Paragraph(Text("The types C, I and O range independently over arbitrary universes, without finiteness or inhabitedness assumptions. Run means that some finite Trace joins the given Frames. Initialization is the Frame with state initial, acquired count zero and empty output. Safety(action,initial,Record) means that for every source a and input r satisfying Record(a,r), every finite Run from initialization on full(r), and every natural position p below its output length, the emitted symbol at p equals a(p). Liveness(action,initial,Record,InD) means that for every such Record with InD(a) and every natural position p, some finite Run from initialization on full(r) emits more than p symbols. In the address formula, s and otherCut denote arbitrary reachable Frames: the phrase equal cut states refers to their equal readable states, and neither Ready nor Cut is required. Only a must satisfy InD; the acquired counts need not coincide.")),
            Describe.Lean(DescribeId.Create("decoder-operation-trace-replay"),DeclarationHandle.Create(Prefix+"trace_replay"),
                H("Unread suffix replay with independent old output"),StatementSource.FromAuthor(Replay()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Op has internal(next,batch), acquire(input to Option(next,batch)), and stopped. Step has only the two original internal and successful available acquisition rules. Frame consists of the original readable state and external acquired count and output word. action reads only the state. Trace retains its entire state vertex list and every finite edge batch. full(r)(q)=some(r(q)). Replay preserves that vertex list exactly, accumulates the actual acquisition and output increments, and changes neither state identity nor batches. Offset and old-output changes are external bookkeeping. Partial acquisition and unreachable loops remain allowed."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-actual-address-equality"),DeclarationHandle.Create(Prefix+"actual_address_eq"),
                H("Live actual addresses agree after equal-state replay"),StatementSource.FromAuthor(Addresses()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Safety means that on every Record every emitted position in every finite primitive run equals its source address. Liveness is positionwise and restricted to InD. Equal cut states, equal cumulative words and one equal unread suffix imply address equality: choose a liveness witness beyond both the requested position and old output, compare actual paths, replay the continuation, and apply safety on both records. No replay or joint injection is a premise."))),DescribeRole.Theorem))));
}
