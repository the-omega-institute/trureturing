using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.DecoderOperationTrace;
internal sealed class BasicDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/DecoderOperationTrace/Basic.";
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
    private static Formula Nat => I("Nat");
    private static Formula Frame(Formula c,Formula q,Formula o) => Call("frame",c,q,o);
    private static Formula Initial => Frame(I("initial"),D(0),I("nil"));
    private static Formula RecordType => Fn(Fn(Nat,I("O")),Fn(Fn(Nat,I("I")),I("Prop")));
    private static Formula FrameType => Call("Frame",I("C"),I("O"));
    private static Formula ActionType => Fn(I("C"),Call("Op",I("C"),I("I"),I("O")));
    private static Formula Run(Formula r,Formula s,Formula t) => Call("Run",I("action"),Call("full",r),s,t);
    private static Formula Live => Call("Liveness",I("action"),I("initial"),I("Record"),I("InD"));
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
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite primitive traces retain actual readable states and acquisition boundaries.",
        H("Primitive decoder trace foundations"),Blocks(
            Describe.Lean(DescribeId.Create("decoder-operation-actual-cut-exists"),DeclarationHandle.Create(Prefix+"actual_cut_exists"),
                H("Position liveness supplies every actual D cut"),StatementSource.FromAuthor(Cuts()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Ready means acquire or stopped. A Cut is a finite trace over the available front(r,n), from the physical initial state with acquired zero and empty output, ending Ready at acquired n. No End event is supplied. Processing means a finite internal-only startup drain and a finite internal-only drain after every acquisition actually executed on any Record. It quantifies neither over unreachable states nor impossible acquisitions. Liveness means every position has a finite full-run witness for every Record in InD. Startup gives n=0. Deterministic path comparability and liveness beyond the current finite output force the next acquisition; its actual drain supplies the next cut. This is an explicit operational theorem. Universal correspondence to a prose machine definition, endpoint granularity require independent assessment; finite startup is derived from actual first-label competitors by processing_of_safe_live_pair."))),DescribeRole.Theorem))));
}
