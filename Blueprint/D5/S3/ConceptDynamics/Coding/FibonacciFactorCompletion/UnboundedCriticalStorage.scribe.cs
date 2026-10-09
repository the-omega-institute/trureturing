using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class UnboundedCriticalStorageDocument : IScribeDocumentDefinition
{
    private static Formula I(string n) => F.Id(n);
    private static Formula.BoundVariable B(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula All(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.ForAll, [..v], p);
    private static Formula Ex(Formula p, params Formula.BoundVariable[] v) => new Formula.BindMany(FormulaQuantifier.Exists, [..v], p);
    private static Formula And(params Formula[] p) { var r=p[^1]; for(var k=p.Length-2;k>=0;--k) r=new Formula.Logic(p[k],FormulaLogicOperator.And,r); return r; }
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a, Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Le(Formula a, Formula b) => Call("le",a,b);
    private static Formula Lt(Formula a, Formula b) => Call("lt",a,b);
    private static Formula Sub(Formula a, Formula b) => Call("subtract",a,b);
    private static Formula Mul(Formula a, Formula b) => Call("multiply",a,b);
    private static Formula Cast(Formula a) => Call("toReal",a);
    private static Formula Nat => I("Nat");
    private static Formula Config => I("Configuration");
    private static Formula Addr => Fn(Nat,I("Label"));
    private static Formula Colors => Fn(Nat,I("Color"));
    private static Formula Frame => Call("Frame",Config,I("Label"));
    private static Formula Record(Formula a, Formula r) => Call("OperationRecord",I("o"),I("lam"),I("contract"),a,r);
    private static Formula RecordFn => Call("OperationRecord",I("o"),I("lam"),I("contract"));
    private static Formula Start => Call("frame",I("initialConfiguration"),D(0),Call("nil",I("Label")));
    private static Formula Run(Formula r, Formula t) => Call("Run",I("action"),Call("full",r),Start,t);
    private static Formula Output(Formula t) => Call("output",t);
    private static Formula Length(Formula t) => Call("length",Output(t));
    private static Formula Peak(Formula n) => Call("Peak",I("action"),I("initialConfiguration"),RecordFn,I("encoding"),n);

    public DocumentDefinition Create()
    {
        var a=I("a"); var r=I("r"); var t=I("t"); var p=I("p"); var n=I("N"); var b=I("B");
        var safety=All(Imp(Record(a,r),All(Imp(Run(r,t),All(Imp(Lt(p,Length(t)),
            Equal(Call("getElem",Output(t),p),Call("apply",a,p))),B("p",Nat))),B("t",Frame))),B("a",Addr),B("r",Colors));
        var live=All(Imp(And(Record(a,r),Call("OperationFiniteSource",a)),All(Ex(And(Run(r,t),Lt(p,Length(t))),B("t",Frame)),B("p",Nat))),B("a",Addr),B("r",Colors));
        var reachable=Call("setOf",F.Seq(Open,I("c"),Sp,Colon,Sp,Config,Sp,Mapsto,Sp,
            Ex(Call("ReachThrough",I("action"),I("initialConfiguration"),RecordFn,I("H"),I("c")),B("H",Nat)),Close));
        var assumptions=And(Call("Processing",I("action"),I("initialConfiguration"),RecordFn),safety,live,
            Call("InjOn",I("encoding"),reachable));
        var bound=All(Imp(Le(Peak(n),Call("toWithTopNat",b)),Le(Sub(Sub(Mul(I("alphaInfinity"),Cast(n)),
            Mul(D(1,0,7),I("alphaInfinity"))),D(1)),Cast(b))),B("N",Nat),B("B",Nat));
        var theorem=All(Imp(assumptions,bound),B("Configuration",I("Type")),
            B("action",Fn(Config,Call("Op",Config,I("Color"),I("Label")))),B("initialConfiguration",Config),
            B("o",I("Ownership")),B("contract",I("Contract")),B("encoding",Fn(Config,Call("List",I("Bool")))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual unbounded return counts give an all-horizon lower bound for complete primitive states.",H("Critical complete storage"),Blocks(
            Paragraph(Text("The original paired sources share one positive return list, the fixed length-twenty-six stem, and their prescribed high and low tails. Every list is supplied at the critical budget for each of the closed, strict and individual-record-margin error contracts. A record margin exists because nonzero errors have finite departure support; no common positive margin is assumed.")),
            Describe.Lean(DescribeId.Create("fib-unbounded-critical-decoder-storage"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/UnboundedCriticalStorage.critical_decoder_storage"),
                H("Complete primitive storage bound"),StatementSource.FromAuthor(Disp(theorem)),AssessedProvenance.FromRepo(),Blocks(
                Paragraph(Text("Configuration is the complete readable primitive state. Processing must terminate at each actual acquisition; safety holds on every actual legal source record, and liveness supplies every position on every eventually-zero source. The encoding is injective on all reachable complete states. Intermediate workspace, readable control, counters, positions, timing and output-side data belong to the state. Frame acquisition and output fields are proof bookkeeping and provide no input to the action.")),
                Paragraph(Text("At checkpoint twenty-six plus twice n, the same first future and empty past output separate all returnCount n sources. Binary strings of length at most B have capacity two to the B plus one minus one. For horizons at least eighty-eight, take n equal to the floor of N minus twenty-six divided by two. The count estimate loses eighty alpha, the stem twenty-six alpha, parity at most one alpha, and variable-length coding one bit. Nonnegative storage handles smaller horizons. A peak of infinity is permitted; the implication applies whenever the peak has a finite bound.")),
                Paragraph(Text("The theorem concerns the stated primitive-operation model. A representation of every prose decoder in this model and the original closed-observation online upper construction are separate requirements. The lower bound alone establishes neither an optimal coefficient nor a matching memory order."))),DescribeRole.Theorem))));
    }
}
