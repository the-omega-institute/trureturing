using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;
internal sealed class NativeFreshSensorAcquisitionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One actual native execution binds the complete rational sector to its material and genuine raw designated sensors.", H("Complete native fresh-sensor sector"), Blocks(
        Describe.Lean(DescribeId.Create("nativefreshsensoracquisition-completenativesector"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorAcquisition.complete_native_sector"),
            H("Same-execution material, raw bindings and all-time sector"), StatementSource.FromAuthor(Complete()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The original t is any finite native Source satisfying D, the original LAB birth condition. The conclusion applies in particular to every earned branching source with at least three original leaves and every positive finite disjoint beta-cherry family. No Positive-image assumption is added. Cherries records literal beta-beta subtrees and disjoint cones; vector at offsets empty,L,LL,LLL,R,LR gives a,b,c,d,e,f, and half=(a-c)/2. All equations hold at every ambient address. The operation B is the actual native neighbor sum of grown(t), not a supplied matrix. Observation is restriction to the sensors list, exactly one terminal per original leaf, so it has b coordinates. The three count equations retain the distinction between all terminals and designated sensors.")),
                Paragraph(Text("oldField is the complete old owner-pair preparation x(theta); zeroExtend is the literal old-cell inclusion E. The native run performs P;S at each original alpha and S;S-left at each original beta in fixed left-to-right order, before any Tick. Its y equals E x(theta) on the actual attained material. Inherited sends alpha labels to LL and beta labels to LLL; fresh lists alpha R and beta R then LR, with branch prefixes and global allocation order. Every designated sensor is both a current terminal and the destination of an actually allocated integer label in that same run.")),
                Paragraph(Text("Installation includes an authentic exhaustive original raw table with all old identifiers below next, genuine current and fresh grants, original root/orientation, exact rational arithmetic, Hold, exclusive complete serialization and sufficient finite backing. Absent, branch, wrong-type, RangeRefusal, BadFrame, proper pending prefixes and disabled missing-right dispatch keep their original meanings; every transaction consumes all output, End, acknowledgement and Return. Physical conformance, true zero origin and record isolation remain ASSUMED-UNVERIFIED premises. There is no Reset, clone, interior numerical port, competing writer or timing/allocation/provider side channel. The theorem concerns a mathematical sector: H(theta) generally differs from the attained E x(theta). It claims neither acquisition of H(theta) nor equality of complete future service. BH(theta) may be visible at nondesignated terminals. Rights survive; restriction by observation is only the designated sensing policy."))), DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Q(string n, Formula t, Formula f) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Ex(string n, Formula t, Formula f) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula A(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Im(Formula x, Formula y) => Seq(P(x), Sp, Rightarrow, Sp, P(y));
    private static Formula In(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(P(x), Sp, Plus, Sp, P(y));
    private static Formula Sub(Formula x, Formula y) => Seq(P(x), Sp, Minus, Sp, P(y));
    private static Formula Scale(byte n, Formula x) => Seq(D(n), Sp, Cdot, Sp, P(x));
    private static Formula Half(Formula x) => Seq(Frac, Grp(x), Grp(D(2)));
    private static Formula Bind(string[] ns, Formula[] ts, Formula f) { for(int i=ns.Length-1;i>=0;--i) f=Q(ns[i],ts[i],f); return f; }
    private static Formula Ands(params Formula[] fs) { var f=fs[^1];for(int i=fs.Length-2;i>=0;--i)f=A(fs[i],f);return f; }
    private static Formula Source => C("Source");
    private static Formula Addr => C("Address");
    private static Formula Val => C("Value");
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat => Seq(Mathbb, Grp(V("Q")));
    private static Formula Zed => Seq(Mathbb, Grp(V("Z")));
    private static Formula G(Formula t) => C("grown",t);

    private static Formula Vec(Formula p,string z)=>C("vector",p,C(z));
    private static Formula B(Formula t,Formula x)=>C("adjacency",G(t),x);
    private static Formula PowB(Formula t,byte n,Formula x)=>C("iterate",C("adjacency",G(t)),D(n),x);

    private static Formula Acts(Formula t,Formula p) {var a=Vec(p,"empty");var b=Vec(p,"L");var c=Vec(p,"LL");var d=Vec(p,"LLL");var e=Vec(p,"R");var f=Vec(p,"LR");
        return Ands(Eqn(B(t,a),Add(b,e)),Eqn(B(t,b),Add(Add(a,c),f)),Eqn(B(t,c),Add(b,d)),Eqn(B(t,d),c),Eqn(B(t,e),a),Eqn(B(t,f),b)); }
    private static Formula Powers(Formula t,Formula p) {var a=Vec(p,"empty");var c=Vec(p,"LL");var d=Vec(p,"LLL");var e=Vec(p,"R");var f=Vec(p,"LR");var h=C("half",p);
        return Ands(Eqn(B(t,h),Half(Sub(e,d))),Eqn(B(t,B(t,h)),h),Eqn(PowB(t,2,a),Add(Add(Scale(2,a),c),f)),Eqn(PowB(t,2,f),Add(Add(a,c),f)),Eqn(PowB(t,4,a),Add(Add(Scale(6,a),Scale(5,c)),Scale(4,f)))); }
    private static Formula Complete() {
        var t=V("t");var k=V("k");var ch=V("ch");var l=V("labels");var n=V("next");var th=V("theta");
        var r=V("result");var m=V("after");var y=V("y");var p=V("p");var i=V("i");var j=V("j");var eta=V("eta");
        var a=C("fst",C("composition",t));var c=C("snd",C("composition",t));var f=C("fresh",t);
        var param=Seq(C("Fin",k),Sp,To,Sp,Rat);var h=C("H",ch,eta);var root=C("root",ch,i);
        var body=Ands(
            Eqn(C("nativeRun",t,l,n,C("oldField",ch,th),C("calls",t)),C("some",C("tuple",G(t),r,m,y))),
            C("D",G(t)),Q("p",Addr,Im(In(p,C("material",t)),In(p,C("material",G(t))))),
            Q("p",Addr,Im(In(p,C("material",G(t))),Eqn(C("coordinate",y,p),C("coordinate",C("zeroExtend",t,C("oldField",ch,th)),p)))),
            Eqn(m,Add(n,C("length",f))),
            Q("i",Zed,Im(C("lt",i,n),Im(In(C("apply",l,i),C("terminals",t)),Eqn(C("apply",r,i),C("inherited",t,C("apply",l,i)))))),
            Q("j",Nat,Im(C("lt",j,C("length",f)),Eqn(C("apply",r,Add(n,j)),C("get",f,j)))),
            Q("p",Addr,Im(In(p,C("sensors",t)),Ex("i",Zed,A(C("le",n,i),Eqn(C("apply",r,i),p))))),
            Eqn(Add(C("length",C("material",G(t))),D(1)),Add(Scale(5,a),Scale(7,c))),
            Eqn(C("length",C("terminals",G(t))),Add(Scale(2,a),Scale(3,c))),
            Eqn(C("length",C("sensors",t)),C("length",C("leaves",t))),
            Q("p",Addr,Im(In(p,C("sensors",t)),In(p,C("terminals",G(t))))),
            Q("i",C("Fin",k),Acts(t,root)),Q("i",C("Fin",k),Powers(t,root)),
            Q("i",C("Fin",k),A(Eqn(C("observation",t,C("half",root)),D(0)),Eqn(C("observation",t,B(t,C("half",root))),D(0)))),
            C("Injective",C("H",ch)),Q("eta",param,Eqn(B(t,B(t,h)),h)),
            Bind(["eta","j"],[param,Nat],Eqn(C("observation",t,C("iterate",C("adjacency",G(t)),j,h)),D(0))),
            Bind(["eta","p"],[param,Addr],Im(In(p,C("terminals",G(t))),Eqn(C("coordinate",h,p),D(0)))));
        return Q("t",Source,Im(C("D",t),Bind(["k","ch","labels","next","theta"],[Nat,C("Cherries",t,k),C("RawMap"),Zed,param],
            Ex("result",C("RawMap"),Ex("after",Zed,Ex("y",Val,body))))));
    }
}
