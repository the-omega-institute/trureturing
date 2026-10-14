using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;
internal sealed class DecoderStartupDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/DecoderStartup.";
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
    private static Formula Acquired(Formula s) => Call("acquired",s);
    private static Formula Add(Formula a,Formula b) => Call("add",a,b);
    private static Formula Append(Formula a,Formula b) => Call("append",a,b);
    private static Formula Frame(Formula c,Formula q,Formula o) => Call("frame",c,q,o);
    private static Formula Initial => Frame(I("initial"),D(0),I("nil"));
    private static Formula RecordType => Fn(Fn(Nat,I("O")),Fn(Fn(Nat,I("I")),I("Prop")));
    private static Formula FrameType => Call("Frame",I("C"),I("O"));
    private static Formula ActionType => Fn(I("C"),Call("Op",I("C"),I("I"),I("O")));
    private static Formula Run(Formula r,Formula s,Formula t) => Call("Run",I("action"),Call("full",r),s,t);
    private static Formula Safety => Call("Safety",I("action"),I("initial"),I("Record"));
    private static Formula Live => Call("Liveness",I("action"),I("initial"),I("Record"),I("InD"));
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
        "Finite actual acquisition and first-label competitors determine decoder startup.",
        H("Finite decoder startup"),Blocks(
            Paragraph(Text("Op consists of internal(next,batch), acquire(input to Option(next,batch)), and stopped. A Frame records a readable state, an external acquired count and an output word; action reads only the state. A finite Run uses internal steps and successful available acquisitions, retaining every intermediate state. The full input has full(r)(q)=some(r(q)). Ready means stopped or acquire. A Drain is a finite Run with no available input ending Ready, so every step is internal. Processing requires a Drain at initialization and after each actually successful acquisition on any Record. The types C, I and O range independently over arbitrary universes; no finiteness or inhabitedness assumption is imposed.")),
            Describe.Lean(DescribeId.Create("decoder-operation-initial-drain"),DeclarationHandle.Create(Prefix+"initial_drain_of_acquired_run"),
                H("An actual acquired run contains finite startup"),StatementSource.FromAuthor(Startup()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A finite Run whose acquired count is positive contains a first acquisition. Its preceding retained prefix consists solely of internal operations and ends at the actual acquire state. Transfer to the empty available input gives a Drain from physical initialization. Every prefix vertex is retained; neither global computation bounds nor termination on unreachable states are required."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decoder-operation-processing-from-competitors"),DeclarationHandle.Create(Prefix+"processing_of_safe_live_pair"),
                H("Actual first-label competitors derive startup from the recovery contract"),StatementSource.FromAuthor(ProcessingFromCompetitors()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Safety means that for every Record(a,r), every finite Run from initialization on full(r), and every p below its output length, the emitted symbol at p equals a(p). Liveness means that for every Record(a,r) with InD(a) and every natural position p, some finite Run on full(r) emits more than p symbols. The two supplied actual records have different first source labels; only the first needs InD liveness. Its live first output cannot occur with zero acquisitions, since the same internal prefix transfers to the competitor and safety would equate their first labels. The acquired run therefore supplies finite startup. Processing then follows from that derived drain and the displayed drains after every actual successful acquisition. Post-acquisition finiteness is not inferred from safety alone. The state C must contain all readable memory, and action must describe the actual internal and acquisition instructions for this operational model to represent a physical decoder."))),DescribeRole.Theorem))));
}
