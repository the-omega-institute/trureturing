using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFibonacciActiveTableDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFibonacciActiveTable", H("NativeFibonacciActiveTable"), Blocks(
            Paragraph(Text("For h stages, dimension(h) is the least d with fib(d plus two) at least h plus one. The compiled Fibonacci stage path provides z(0) through z(h) at that exact dimension. The complete word is z(stage) followed by zero, accumulator, zero and four latch bits in the order L00, L01, L10, L11. Every mutable coordinate is in this one word, of width dimension(h) plus seven.")),
            Paragraph(Text("Q(i,a) uses stage i and empty latch. B(i,a,b) uses stage i and the one-hot latch at (b,i modulo two). C(i,b) uses stage i plus one, accumulator b, and that same latch. V(a,first), V(a,second), V(a,route) use stage zero, accumulator a, and latches 0100, 0101, 0001. Distinct stage words separate stages. At any shared stage, B and C use opposite parity positions. At stage zero there is no C, and B uses parity zero while both one-hot V latches use parity one. The two-hot V latch is distinct from all other latches. Both accumulator choices remain installed. This proves injectivity even for empty actual supports.")),
            Paragraph(Text("Installed is exactly the image of every Control h: two Q states at each of h plus one stages, four B states and two C states at each of h stages, and six V states. Thus the installed cardinality is eight h plus eight. When h is zero, the eight Q and V words are retained, and both Q words are halts. The nativeProgram takes immutable addresses directly, so its table and edges at h equal to zero do not depend on an uninhabited Chart zero. Actual full source trees have positive length.")),
            Paragraph(Text("At a nonterminal Q the literal is its original chart address followed by K right edges. At the pilot, alpha selects B(0,a,a), beta selects B(0,a,not a), branch holds Q(0,a), and absent selects V(a,first). At positive stages all four replies select B(i,a,a XOR chi(reply)), with chi true exactly on beta and absent. Every B performs a paid root Read: if a differs from b it selects B(i,b,b); otherwise it selects C(i,b). Every C performs a paid root Read and selects Q(i plus one,b). V first and second each perform a genuine Update, then V route performs a paid root Read and returns to Q(0,a) on every reply. Q(h,a) has fixed Stop payload a.")),
            Paragraph(Text("All words avoid adjacent ones because the stage word is legal and the accumulator has zero separators. Each nonhold typed row changes exactly one bit. Data adds one latch bit; correction changes the accumulator; stage advance uses one Fibonacci path edge; clearing removes one latch bit. The polling latch square is 0000, 0100, 0101, 0001, 0000. Only the two pilot branch rows hold when h is positive. No unsupported Read row is changed, no paid root Read is removed, and no internal instruction is inserted.")),
            Paragraph(Text("Support and EncodedSupport contain exactly the target/current-Source pairs reached at a specified complete control by an actual n-step prefix, with epoch and log existentially quantified. Their equality is proved for arbitrary entry families and includes empty supports. FirstHalt means an actual finite Run with the stated number of remaining actions and fixed payload, and no shorter terminating Run with any payload. RankDescent exposes the next actual source, epoch and single event, reduces the remaining primitive count by one, and proves a one-bit change on every finite terminating primitive. A pilot self-hold cannot occur on such a terminating Run: the same control and source would have a shorter terminating suffix, contradicting determinism. The all-row table still retains those holds.")),
            Describe.Lean(DescribeId.Create("native-fibonacci-active-table"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciActiveTable.native_fibonacci_active_table"),
                H("Complete active word table"), StatementSource.FromAuthor(Disp(TableStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement includes minimal Fibonacci dimension, injectivity, legality, exact installed count, every typed row, actual native conjugacy, exact support equality, first-halt equivalence, and actual rank descent. The identity address map preserves the literal itself. Extra ambient cube adjacencies do not add instructions. Static constructions and comparison-class minimum-width lower bounds are outside this active construction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("encoded-active-parity-execution"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciActiveTable.encoded_active_parity_execution"),
                H("Same-source original parity trace"), StatementSource.FromAuthor(Disp(ExecutionStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original native_active_parity_execution theorem is applied on the same full original skeleton, every independent label assignment and the same unknown entry t. Its finite guarded Run is lifted instruction by instruction to NativeSerialMachine.Run, with the same Read epoch, literal and raw reply and the same Update successor. An explicit Stop endpoint supplies the finite suffix. The exact genuine Update count is twice the difference between K and floor((t plus bit(x(0))) divided by two). The conditions are t at most twice K and either even original leaf count or t equal to zero. No claim is made for the excluded odd-entry regime. actual_register_execution certifies the same source evolution, chronological log and every literal truth. The fixed original parity payload is preserved. The existing event-cost vector is preserved in all five coordinates; no absolute three-h plus four-k plus c bill is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("first-of-run"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeFibonacciActiveTable.first_of_run"),
                H("Actual Run fixes the first halt"),StatementSource.FromAuthor(Disp(FirstStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every control type C, native instruction function, initial control, epoch and source, any terminating actual native Run reaches its first halt at precisely the length of its complete trace, with the same fixed output. A purported shorter remaining execution contradicts native run uniqueness. The statement retains the arbitrary native machine and actual source; it requires neither a finite control carrier nor an encoding premise. The static scan uses this identity for its exact first-halt count and each remaining suffix."))),DescribeRole.Theorem))));

    private static Formula FirstStatement() {
        var C=V("C"); var delta=V("delta"); var c=V("c"); var j=V("j"); var u=V("u"); var trace=V("trace"); var a=V("a");
        return All("C",V("Type"),All("delta",Arr(C,Call("Op",C,V("Bool"))),All("c",C,All("j",V("Nat"),All("u",V("Source"),
            All("trace",V("Trace"),All("a",V("Bool"),Imp(Call("Run",delta,c,j,u,trace,a),
                Call("FirstHalt",delta,c,j,u,Call("length",trace),a)))))))));
    }
    private static Formula TableStatement() {
        var h=V("h"); var a=V("a"); var K=V("K"); var c=V("c"); var d=V("d");
        var dim=Call("dimension",h); var p=Call("path",h); var e=Call("encodingEquiv",p); var f=Call("nativeProgram",a,K);
        var j=V("j"); var u=V("u"); var n=V("n"); var b=V("b"); var E=V("E"); var initial=V("initial"); var target=V("target");
        var supports=All("E",V("Type"),All("initial",Arr(E,V("Source")),All("target",Arr(E,V("Bool")),All("c",Call("Control",h),
            Eq(Call("EncodedSupport",p,a,K,E,initial,target,Call("encodingEquiv",p,c)),Call("Support",a,K,E,initial,target,c))))));
        var first=All("c",Call("Control",h),All("j",V("Nat"),All("u",V("Source"),All("n",V("Nat"),All("b",V("Bool"),
            IffOf(Call("FirstHalt",Call("encodedProgram",p,a,K),Call("encodingEquiv",p,c),j,u,n,b),Call("FirstHalt",f,c,j,u,n,b)))))));
        var result=And(Le(Add(h,D(1)),Call("fib",Add(dim,D(2)))),
            All("d",V("Nat"),Imp(Lt(d,dim),Lt(Call("fib",Add(d,D(2))),Add(h,D(1))))),
            Call("Injective",Call("encode",p)),All("c",Call("Control",h),Call("Adm",Add(dim,D(7)),Call("encode",p,c))),
            Eq(Call("card",Call("Installed",p)),Add(Seq(D(8),h),D(8))),Call("AllRows",p,a,K),Call("Certificate",e,f),supports,first,Call("RankDescent",p,a,K));
        return All("h",V("Nat"),All("a",Arr(Call("Fin",h),V("Address")),All("K",V("Nat"),result)));
    }
    private static Formula ExecutionStatement() {
        var S=V("S"); var x=V("x"); var t=V("t"); var K=V("K"); var trace=V("trace");
        var h=Call("length",S); var C=Call("chartOf",S); var address=Call("address",C); var p=Call("path",h);
        var e=Call("encodingEquiv",p); var initial=Call("iterate",V("substitution"),t,Call("source",C,x));
        var old=Call("nativeProgram",address,K); var encoded=Call("encodedProgram",p,address,K);
        var a=Call("parity",Call("labels",x),h); var start=Call("start",h); var count=Seq(D(2),Par(Seq(K,Sp,Minus,Sp,Call("div",Add(t,Call("bit",Call("x",D(0)))),D(2)))));
        var w=V("w"); var J=V("J"); var n=V("n"); var q=V("q"); var y=V("y"); var m=V("m");
        Formula Config(Formula control,Formula epoch,Formula source,Formula log) => Call("config",control,epoch,source,log);
        var evolution=Ex("w",Call("Installed",p),Ex("J",V("Nat"),And(
            Call("Reaches",Call("nativeStep",encoded),Config(Call("encodingEquiv",p,start),D(0),initial,Call("nil")),
                Config(w,J,Call("iterate",V("substitution"),J,initial),trace)),
            Eq(Call("encodedProgram",p,address,K,w),Call("stop",a)),
            All("n",V("Nat"),All("q",V("Address"),All("y",V("Reply"),Imp(Call("member",Call("read",n,q,y),trace),
                Eq(Call("readout",q,Call("iterate",V("substitution"),n,initial)),y))))))));
        var result=Ex("trace",V("Trace"),And(Call("Run",old,start,D(0),initial,trace,a),
            Call("Run",encoded,Call("encodingEquiv",p,start),D(0),initial,trace,a),
            Call("FirstHalt",old,start,D(0),initial,Call("length",trace),a),Eq(Call("updates",trace),count),
            All("m",V("CostModel"),Eq(Call("cost",m,trace,D(0)),Call("length",trace))),evolution));
        var admissible=Seq(Par(Eq(Call("mod",h,D(2)),D(0))),Sp,Lor,Sp,Par(Eq(t,D(0))));
        return All("S",V("Source"),All("x",Arr(Call("Fin",h),V("Bool")),All("t",V("Nat"),All("K",V("Nat"),
            Imp(Le(t,Seq(D(2),K)),Imp(admissible,result))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(Par(a), Sp, To, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] xs) {
        var r = xs[^1];
        for (int i = xs.Length-2; i >= 0; --i) r = Seq(Par(xs[i]), Sp, Land, Sp, Par(r));
        return r;
    }
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Ex(string n, Formula t, Formula b) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
