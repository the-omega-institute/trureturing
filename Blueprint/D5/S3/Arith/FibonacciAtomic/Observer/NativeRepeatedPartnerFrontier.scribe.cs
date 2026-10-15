using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeRepeatedPartnerFrontierDocument : IScribeDocumentDefinition
{
    private const string Prefix="D5/S3/Arith/FibonacciAtomic/Observer/NativeRepeatedPartnerFrontier.";
    public DocumentDefinition Create()=>DocumentDefinition.Create(ScribeNode.Create(
        "The exact jointly optimized complete-entry and total-state frontier holds on the entire original native repeated-partner origin fiber.",
        H("Exact Native Total-State Frontier"),Blocks(
            Paragraph(Text("Solves(M,entry,r,q) quantifies every actual origin in NativeSixSourceCones.Fiber. The entire exported and recoverable initial mutable state is entry(x) in Q+H. A finite set E covers its realized range with cardinality at most r; because Q+H is finite this is exactly an upper bound on realized export capacity. For every origin there is a terminating actual stationary Run with at most q running visits and fixed whole-row output canonicalRow(P,x). Tables, addresses, state spaces and outputs are common across all origins. All members of Q and H are charged, including unreachable states. The arbitrary function entry is quantified together with the common controller; no particular encoder is fixed in the lower theorem.")),
            Describe.Lean(DescribeId.Create("nativerepeatedpartnerfrontier-native-budget-lower"),
                DeclarationHandle.Create(Prefix+"native_budget_lower"),H("Native Capacity and State Bounds"),
                StatementSource.FromAuthor(Disp(Lower(true))),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("The exact all-address factorization of the six actual sources is used at each visited running state. Its two possible native replies define two common successors for that state. Bounded unrolling produces a finite set of possible halts with cardinality at most two to the power q. The five distinct complete predecessor rows require five distinct halts. Taking the union over at most r actual entry values gives five at most r times two to the power q. Binary replies are asserted only on these actual sources, not on the full native interface or every origin.")),
                    Paragraph(Text("For the state bound let R be the union of running states in these actual terminating runs and V their disjoint running and terminal states. All five distinct required halts occur in V, so its cardinality is at least card(R)+5. The run-support lemma proves that every vertex in V is either an exported entry or one of the two native successors of a member of R. Therefore card(V) is at most r+2card(R), and five is at most r+card(R). Counting the entire Q+H gives total at least max(5,10-r). This is the reachable-graph counting method applied to the exact native reply restriction. It imposes no acyclicity, unique-predecessor, tree-controller or non-repetition assumption."))),DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("nativerepeatedpartnerfrontier-exact-frontier"),
                DeclarationHandle.Create(Prefix+"exact_frontier"),H("All Upper Budgets"),
                StatementSource.FromAuthor(Disp(Exact())),AssessedProvenance.FromRepo(),Blocks(
                    Paragraph(Text("Minimum(r,q) is ten when r=1 and q=3, and max(5,10-r) otherwise. The first conjunct is universal over all finite running and halting types, every common controller and every complete-entry encoder. It proves infeasibility whenever r times two to the power q is less than five, and the minimum lower bound whenever a successful controller exists. The second conjunct constructs a controller with exactly that minimum at every feasible budget, using five fixed complete-row halts. Thus nonexistence represents the infinite branch of the original minimum formula; no finite substitute or fixed-encoder performance statement is used.")),
                    Paragraph(Text("At capacity one, the complete-entry cover has at most one member, so all actual origins have one common entry. The previously proved six-source three-call obstruction gives ten states at (1,3). All other state lower bounds use native_budget_lower. The six matching full-fiber constructions supply ten at (1,3), nine for r=1 and q at least four, eight for r=2 and q at least two, seven for r=3 and q at least one, six for r=4 and q at least one, and five for r at least five. Elementary integer case analysis exhausts every feasible r at least one and natural q. Capacity and invocation limits are upper bounds, so the construction adds no dummy queries or exported distinctions.")),
                    Paragraph(Text("The domain, all literal addresses, repeated partner occurrences, complete predecessor rows and entire mutable-state contract are unchanged. Genuine acquisition, same-version authentication, actual export, recoverable normalization, access isolation and native-service continuity remain supplied premises. The frontier counts abstract states and actual native calls. It identifies neither exported capacity with running memory nor state cardinality with physical storage, production cost, address price or time. Existing native chart and finite-root suppliers remain the source of their reused statements; the new content is the actual six-source restriction, forced five-address obstruction, full-fiber common controllers and their exact state frontier. No literature-priority claim is made."))),DescribeRole.Theorem))));
    private static Formula Lower(bool halts)
    {
        var q=V("Q");var h=V("H");var m=V("M");var e=V("entry");var r=V("r");var t=V("q");
        var cap=LeOf(D(5),Call("mul",r,Call("pow",D(2),t)));
        var bound=LeOf(halts?Call("max",D(5),Call("sub",D(1,0),r)):Call("minimum",r,t),Call("card",Call("Sum",q,h)));
        var conclusion=halts?And(cap,LeOf(D(5),Call("card",h)),bound):And(cap,bound);
        var body=All("M",Call("Controller",q,h),All("entry",Fn(V("Fiber"),Call("Sum",q,h)),
            halts?All("r",V("Nat"),All("q",V("Nat"),Imp(Call("Solves",m,e,r,t),conclusion))):Imp(Call("Solves",m,e,r,t),conclusion)));
        return All("Q",V("Type"),All("H",V("Type"),Seq(OpenBracket,Call("Fintype",q),CloseBracket,Sp,
            OpenBracket,Call("Fintype",h),CloseBracket,Comma,Sp,body)));
    }
    private static Formula Exact()
    {
        var r=V("r");var q=V("q");var n=V("n");var m=V("M");var e=V("entry");
        var cap=LeOf(D(5),Call("mul",r,Call("pow",D(2),q)));
        var upper=Some("n",V("Nat"),Some("M",Call("Controller",Call("Fin",n),Call("Fin",D(5))),
            Some("entry",Fn(V("Fiber"),Call("Sum",Call("Fin",n),Call("Fin",D(5)))),And(
                Call("Solves",m,e,r,q),EqOf(Call("add",n,D(5)),Call("minimum",r,q))))));
        return All("r",V("Nat"),All("q",V("Nat"),Imp(LeOf(D(1),r),And(Lower(false),Imp(cap,upper)))));
    }
    private static Formula V(string s)=>F.Id(s);
    private static Formula Par(Formula f)=>Seq(Open,f,Close);
    private static Formula Call(string n,params Formula[] a)=>new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula Fn(Formula a,Formula b)=>Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula LeOf(Formula a,Formula b)=>Seq(a,Sp,Leq,Sp,b);
    private static Formula And(params Formula[] fs)=>Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula Imp(Formula a,Formula b)=>Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula All(string n,Formula t,Formula b)=>Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b)=>Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
