using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class DecoderPeakDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/DecoderPeak.";
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n),t);
    private static Formula All(Formula body, params Formula.BoundVariable[] vars) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,[.. vars],body);
    private static Formula And(params Formula[] p)
    {
        var r=p[^1]; for(var j=p.Length-2;j>=0;j--) r=new Formula.Logic(p[j],FormulaLogicOperator.And,r); return r;
    }
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);
    private static Formula List(Formula a) => Call("List",a);
    private static Formula Nat => I("Nat");
    private static Formula Acquired(Formula s) => Call("acquired",s);
    private static Formula Frame(Formula c,Formula q,Formula o) => Call("frame",c,q,o);
    private static Formula Initial => Frame(I("initial"),D(0),I("nil"));
    private static Formula RecordType => Fn(Fn(Nat,I("O")),Fn(Fn(Nat,I("I")),I("Prop")));
    private static Formula FrameType => Call("Frame",I("C"),I("O"));
    private static Formula ActionType => Fn(I("C"),Call("Op",I("C"),I("I"),I("O")));
    private static Formula Trace(Formula r,Formula s,Formula t,Formula v) => Call("Trace",I("action"),Call("full",r),s,t,v);
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

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete horizon peak bounds every retained primitive trace vertex.",
        H("Primitive decoder horizon peaks"),Blocks(
            Paragraph(Text("The types C, I and O range independently over arbitrary universes, without finiteness or inhabitedness assumptions. The action reads only C. Frame contains the readable state together with the external acquired count and output word. Trace retains the initial state and every state reached by an internal or successful acquisition step; full(r)(q)=some(r(q)). Record is the supplied arbitrary predicate on source and input streams, and encoding is the supplied function from C to finite Boolean lists. The bound requires neither Ready nor Cut, safety, liveness, finite processing nor an injective encoding. The private trace_vertex_split constructs the intermediate Frame and actual prefix and suffix Runs; run_mono bounds its acquired count, and peak_bound includes its supplied cost in the supremum.")),
            Describe.Lean(DescribeId.Create("decoder-operation-peak-trace-bound"),DeclarationHandle.Create(Prefix+"peak_trace_bound"),
                H("All readable vertices belong to the complete horizon peak"),StatementSource.FromAuthor(Vertices()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("ReachThrough(H,c) means some Record has a finite primitive run from physical initialization ending at c with acquired count at most H. Peak is the WithTop Nat supremum of the lengths of the supplied original encodings over all such states. Every trace vertex has its actual prefix run, whose acquired count is no greater than the final count. Initialization, transient workspaces, acquisition states and completed endpoints are included. Infinite peaks are retained. The encoding and its original cost are supplied rather than replaced; no equality with a maximum over chosen cut states is asserted."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-peak-monotone"),
                DeclarationHandle.Create(Prefix+"peak_monotone"),H("The complete horizon peak is monotone"),
                StatementSource.FromAuthor(Disp(All(Call("Monotone",Call("Peak",I("action"),I("initial"),I("Record"),I("encoding"))),
                    B("C",I("Type")),B("I",I("Type")),B("O",I("Type")),B("action",ActionType),B("initial",I("C")),
                    B("Record",RecordType),B("encoding",Fn(I("C"),List(I("Bool"))))))),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every state reachable with at most H acquisitions is reachable with at most K whenever H <= K. Inclusion of these actual reachable states preserves the supremum bound, including infinite peaks and all original encodings."))),DescribeRole.Theorem))));
}
