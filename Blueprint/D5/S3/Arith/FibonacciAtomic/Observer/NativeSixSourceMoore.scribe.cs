using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSixSourceMooreDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceMoore.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Constant complete entry and three stationary native calls require five running states and five disjoint whole-row halting states on the original repeated-partner inverse fiber.",
        H("Three Calls Force Ten Total States"), Blocks(
            Paragraph(Text("The comparison domain is the entire infinite OriginFiber(P,row) from NativeSixSourceCones. It contains every finite origin whose one-step image has the exact complete depth-three row with classes a,b1,a,b2,c,b3,c,b4 and all cross-class disequalities. The six fixed actual origins from that module are a restriction used only in the lower proof. The native interface still permits every finite address and all four replies.")),
            Paragraph(Text("A controller has arbitrary finite types Q and H. Its complete state is their disjoint sum. Every member of Q has one fixed literal address and four fixed successor entries. Every member of H has one fixed complete LiteralRow output. All tables are common to every source. All states, including unused states, are counted. A halt consumes no invocation. Each running visit consumes exactly one invocation, including repeated visits, deep addresses and absence. A mathematical Run trace records those visits for the proof and is not additional accessible controller storage. Shared states, merging histories, cycles across runs, early halts and halting entry states are permitted.")),
            Describe.Lean(DescribeId.Create("nativesixsourcemoore-three-call-state-obstruction"),
                DeclarationHandle.Create(Prefix + "three_call_state_obstruction"), H("Full-Fiber State Obstruction"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each positive right class, compare its actual positive source with the zero source having the same partner beta placement. Their questions agree at every location except that right class. Equal replies along one terminating run reproduce the same terminal state on the other source. Distinct complete predecessor rows exclude that outcome, forcing one actual state at each of the four right-cone locations.")),
                    Paragraph(Text("Suppose no running state has a partner-cone address. Compare the zero-a run with each positive source. On that run only the corresponding positive right cone can separate each pair. Thus all four distinct right-cone locations must occur along the same zero-a run. Its list of running visits has length at most three, a contradiction. A fifth running state therefore has a partner-cone address. The five address locations are disjoint, so their required states are different regardless of shared histories or cycles.")),
                    Paragraph(Text("The five pairwise different canonical predecessor rows require five different terminal states, because the whole output is fixed at each halt. Cardinal monotonicity on the disjoint state sum gives ten total states. The entry variable is one fixed complete mutable state, expressing the constant-export case after the supplied complete-entry normalization. Acquisition, genuine same-version data, actual export, authenticated update continuity, recoverable entry and the complete access cut remain supplied premises. No output decoder, inverse operation or physical storage/time equivalence is provided."))), DescribeRole.Theorem))));
    private static Formula Statement()
    {
        var q=V("Q"); var h=V("H"); var m=V("M"); var entry=V("entry");
        var x=V("x"); var tr=V("tr"); var halt=V("h");
        var success=All("x",V("Fiber"),Some("h",h,Some("tr",Call("List",q),And(
            Call("Run",m,Call("rho",x),entry,tr,halt),
            EqOf(Call("out",m,halt),Call("canonicalRow",V("P"),x)),
            LeOf(Call("length",tr),D(3))))));
        var bound=And(LeOf(D(5),Call("card",q)),LeOf(D(5),Call("card",h)),
            LeOf(D(1,0),Call("card",Call("Sum",q,h))));
        return All("Q",V("Type"),All("H",V("Type"),Seq(
            OpenBracket,Call("Fintype",q),CloseBracket,Sp,OpenBracket,Call("Fintype",h),CloseBracket,Comma,Sp,All("M",Call("Controller",q,h),
            All("entry",Call("Sum",q,h),Imp(success,bound))))));
    }
    private static Formula V(string s)=>F.Id(s);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b)=>Seq(a,Sp,Leq,Sp,b);
    private static Formula And(params Formula[] fs)=>Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
