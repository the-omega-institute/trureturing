using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFibonacciStaticScanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFibonacciStaticScan",H("Complete static native parity scan"),Blocks(
        Paragraph(Text("For an immutable list ps of M literal addresses, the complete control consists of Q(j,a), with j from zero through M, B(j,a,b) and C(j,b), with j less than M, for every Boolean a and b. There are no V states. Initialization is Q(0,false). Q(j,a) reads ps[j] and every one of the four raw replies selects B(j,a,a XOR psi(reply)); psi is true precisely on beta. Unequal B(j,a,b) reads the root and selects B(j,b,b); diagonal B(j,b,b) reads the root and selects C(j,b); C(j,b) reads the root and selects Q(j+1,b). Every routing row ignores its actual raw reply, with all four continuations installed. Q(M,a) has fixed Stop payload a. No local action, Update, hold or extra mutable counter occurs.")),
        Paragraph(Text("The immutable Fibonacci stage path supplies M plus one distinct no-11 words z(j), with consecutive words at Hamming distance one, in dimension d_F(M+1). Four latch coordinates have order L00,L01,L10,L11. The complete physical words are z(j) 0 a 0 0000 for Q, z(j) 0 a 0 e(b,j modulo two) for B, and z(j+1) 0 b 0 e(b,j modulo two) for C. The encoding restricts the existing full active geometry to Q,B,C; it transfers no active dispatch or Update semantics. Installed is exactly the range of this static encoding. Its cardinality is 8M+2 and its width is d_F(M+1)+7, with every typed Read continuation at distance one. The stage/latch distinction separates B from C even when accumulator and latch values agree. Empty actual support does not remove a word.")),
        Paragraph(Text("TableFacts states Fibonacci capacity and the least stage dimension, injectivity, no-11 admissibility, exact installed cardinality, all typed rows, the complete native control conjugacy, equality of every exact finite-prefix support, first-halt equivalence, stationary source and epoch at all reached prefixes, and one-unit remaining-primitive descent with one physical bit change. Supports quantify actual source, target and chronological prefix for any entry family, including empty families. The conjugacy preserves instruction type, literal, raw response, source, epoch, fixed payload, every finite prefix, remaining primitives and all five event-cost coordinates. It installs only the complete physical word.")),
        Paragraph(Text("dataBetaCount(u,ps) denotes the sum of bit(psi(readout(p,u))) over ordered data occurrences; addressSum(ps) denotes the sum of their literal lengths. For a stationary actual source u, block(u,e,p) starts with the actual data Read at p and appends exactly 2+bit(psi(readout(p,u))) root Reads, each with readout([],u). scanTrace concatenates these blocks in list order. accumulate folds XOR of the data contributions from its initial Boolean. Occurrences remain distinct even when a data literal is empty and all raw replies coincide. ExecutionFacts certifies native and encoded Runs of that same trace, first halt, every literal and raw response at epoch zero, zero local actions and Updates, primitive and Read counts equal to trace length, address cost equal to the sum of literal lengths when the address tariff is length, and the exact arbitrary response bill. For a response tariff r, this bill is the sum over p in ps of r(readout(p,u)) plus (2+bit(psi(readout(p,u)))) times r(readout([],u)). Arbitrary address tariffs need not give the root zero cost. Actual native register execution reaches the fixed Stop with epoch zero and unchanged source. At every reached chronological prefix n, its log is exactly the first n events, its remaining native Run is exactly the suffix after n events, and both controls first halt after precisely trace length minus n more Reads. This makes the remaining rank finite on every actual support; the rank is proof data, never an installed register.")),
        Describe.Lean(DescribeId.Create("native-static-complete-scan"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciStaticScan.native_static_complete_scan"),
            H("Full installation and paid scan"),StatementSource.FromAuthor(Disp(Generic())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Induction on the remaining literal list constructs the native Run. The latch route performs two root Reads when the data contribution is zero and three when it is one. Each step advances through the displayed installed control states. Determinism gives the first halt, with no earlier Stop. The complete table includes M=0: there are exactly two Q halts, an empty trace and width seven, without any Chart zero hypothesis. The least-dimension statement concerns the chosen stage path; it asserts no comparison-class optimum for the whole controller."))),DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("original-static-parity-scan"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciStaticScan.original_static_parity_scan"),
            H("Original labels, unknown entry and exact bills"),StatementSource.FromAuthor(Disp(Original())),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Here C is chartOf(S), h is the positive leaf count of the original full ordered skeleton, ps is dataList(C,K), and u is substitution iterated t times on source(C,x). Every original label x(i) is independent. The list is q(0),q(0)R,...,q(0)R^K, then the next original cone, through the last cone. Its length M is h(K+1). addressMass(C) is the sum of the actual leaf address lengths, and depth(C) is their maximum. contributions(x,t) is the sum over i of (t+bit(x(i))) modulo two. The only promises are t at most 2K and either even h or t equal to zero.")),
                Paragraph(Text("The original cone readout theorem and the exact right-clock law give branch before floor(n(i)/2), one terminal alpha or beta at that position, and absent afterwards, where n(i)=t+bit(x(i)). This terminal lies within the installed scan. Beta occurs once iff n(i) is odd; terminal uniqueness does not imply an unconditional beta. Summing only scheduled data occurrences gives contributions(x,t). Their XOR is the original parity because the common entry-parity term cancels for even h and vanishes for t=0. The constructed Run therefore first halts after exactly 3M+contributions(x,t) Reads. Every routing response is still present; for one leaf with K=t=0 and x(0)=true, one scheduled beta produces four actual beta root Reads.")),
                Paragraph(Text("Every data query occurs once as an ordered occurrence in scanTrace. Its actual address bill is (K+1)addressMass(C)+hK(K+1)/2; all root routing addresses have length zero. The maximum data literal length depth(C)+K is attained by a deepest original leaf with its K-right suffix, and the same maximum holds among actual submitted literals. Neither the response tariff nor a physical native-operation cost is fixed by these address formulas. The result supplies a complete static upper construction. Minimum width lower bounds, asymptotic comparison-class optima and minimum Read count are separate questions; the excluded odd-positive-lag regime is not claimed."))),DescribeRole.Theorem))));

    private static Formula Generic() {
        var ps=V("ps"); var u=V("u"); var trace=Call("scanTrace",u,D(0),ps);
        return All("ps",Call("List",V("Address")),All("u",V("Source"),And(
            Call("TableFacts",ps),Call("ExecutionFacts",ps,u,Call("accumulate",u,V("false"),ps),trace),
            Eq(Call("length",trace),Add(Mul(D(3),Call("length",ps)),Call("dataBetaCount",u,ps))))));
    }
    private static Formula Original() {
        var S=V("S"); var x=V("x"); var t=V("t"); var K=V("K"); var h=Call("length",S);
        var C=Call("chartOf",S); var ps=Call("dataList",C,K);
        var u=Call("iterate",V("substitution"),t,Call("source",C,x));
        var trace=Call("scanTrace",u,D(0),ps); var M=Mul(h,Add(K,D(1)));
        var i=V("i"); var r=V("s"); var n=Add(t,Call("bit",Call("x",i)));
        var raw=Call("readout",Call("append",Call("address",C,i),Call("rights",r)),u);
        var cones=All("i",Call("Fin",h),All("s",V("Nat"),And(
            Le(Call("div",n,D(2)),K),IffOf(Eq(raw,V("absent")),Lt(n,Mul(D(2),r))),
            IffOf(Eq(raw,V("alpha")),Eq(n,Mul(D(2),r))),
            IffOf(Eq(raw,V("beta")),Eq(n,Add(Mul(D(2),r),D(1)))),
            IffOf(Eq(raw,V("branch")),Le(Add(Mul(D(2),r),D(2)),n)))));
        var p=V("p");
        var result=And(Call("TableFacts",ps),Eq(Call("length",ps),M),
            Call("ExecutionFacts",ps,u,Call("parity",Call("labels",x),h),trace),
            Eq(Call("length",trace),Add(Mul(D(3),M),Call("contributions",x,t))),
            Eq(Call("addressSum",ps),Add(Mul(Add(K,D(1)),Call("addressMass",C)),Call("div",Mul(Mul(h,K),Add(K,D(1))),D(2)))),
            All("p",V("Address"),Imp(Call("member",p,ps),Le(Call("length",p),Add(Call("depth",C),K)))),
            Ex("p",V("Address"),And(Call("member",p,ps),Eq(Call("length",p),Add(Call("depth",C),K)))),Call("SubmittedMaximum",trace,Add(Call("depth",C),K)),cones);
        return All("S",V("Source"),All("x",Arr(Call("Fin",h),V("Bool")),All("t",V("Nat"),All("K",V("Nat"),
            Imp(Le(t,Mul(D(2),K)),Imp(Or(Eq(Call("mod",h,D(2)),D(0)),Eq(t,D(0))),result))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..xs]);
    private static Formula Eq(Formula a,Formula b) => Seq(a,Sp,F.Eq,Sp,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Lt(Formula a,Formula b) => Seq(a,Sp,F.Lt,Sp,b);
    private static Formula Add(Formula a,Formula b) => Seq(a,Sp,Plus,Sp,b);
    private static Formula Mul(Formula a,Formula b) => Seq(Par(a),Sp,Par(b));
    private static Formula Arr(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula IffOf(Formula a,Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula Or(Formula a,Formula b) => Seq(Par(a),Sp,Lor,Sp,Par(b));
    private static Formula And(params Formula[] xs) {
        var r=xs[^1]; for(int i=xs.Length-2;i>=0;--i) r=Seq(Par(xs[i]),Sp,Land,Sp,Par(r)); return r;
    }
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Ex(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
