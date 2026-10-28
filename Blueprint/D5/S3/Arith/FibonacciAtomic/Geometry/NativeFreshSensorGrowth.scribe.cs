using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeFreshSensorGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fixed original-leaf growth is a successful guarded native execution with fresh-zero rational values.", H("Native fresh sensor growth"), Blocks(
        R("executes", "Execution on every finite native source", Exec(), "Source is the original Bool free magma, with true denoting alpha and false beta. The function grown replaces alpha by (beta,alpha) and beta by ((beta,alpha),alpha). The calls traverse the original leaves from left to right. At alpha they promote then split its owner; at beta they split its owner then its left child. Only guarded structural calls occur. Successful traces lift through the existing native runner in arbitrary output contexts."),
        R("actual_values", "Actual execution and fresh-zero inclusion", Values(), "The raw table and next integer are the actual nativeRun arguments and outputs. Every old material address keeps its original rational value and every new material address receives zero. This is the old-cell inclusion E on the same actual attained source. The installation still presumes authentic exhaustive raw bindings, current and fresh rights, complete exclusive framing, exact arithmetic, Hold and sufficient backing. Physical conformance and record isolation remain installation premises. The separate raw_bindings theorem characterizes every inherited and freshly allocated label on this same run; none of these claims acquires an installation premise."),
        R("inventory", "Full material, terminal and designated counts", Inventory(), "If a and c are the original composition counts, grown(t) has 5a+7c-1 actual material cells and 2a+3c current terminals. There is exactly one designated sensor per original logical leaf, and every such sensor is an actual current terminal. Counts include beta material markers and all nondesignated fresh terminals."),
        R("update_lift", "Ambient parent cancellation for a zero root", LiftLaw(), "The update sums the native neighbors at each material address and is zero outside material. Lift prefixes one edge and assigns zero at every exterior address. The attached root must have value zero; its contribution to the external parent then vanishes. The equation covers every address, including the exterior, and uses no assumed matrix actions."))));
    private static DocumentBlock R(string n, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create("nativefreshsensorgrowth-"+n.Replace("_","")), DeclarationHandle.Create(Prefix+n),
            H(title), StatementSource.FromAuthor(f), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
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
    private static Formula Scale(int n, Formula x) => Seq(D(n), Sp, Cdot, Sp, P(x));
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

    private static Formula Inventory() { var t=V("t");var a=C("fst",C("composition",t));var c=C("snd",C("composition",t));var p=V("p");
        return Q("t",Source,Ands(Eqn(Add(C("length",C("material",G(t))),D(1)),Add(Scale(5,a),Scale(7,c))),
            Eqn(C("length",C("terminals",G(t))),Add(Scale(2,a),Scale(3,c))),
            Eqn(C("length",C("sensors",t)),C("length",C("leaves",t))),
            Q("p",Addr,Im(In(p,C("sensors",t)),In(p,C("terminals",G(t))))))); }
    private static Formula Exec() { var t=V("t"); return Q("t",Source,Eqn(C("run",t,C("calls",t)),C("some",G(t)))); }
    private static Formula Values() {
        var t=V("t");var l=V("l");var n=V("n");var x=V("x");var m=V("m");var j=V("j");var y=V("y");var p=V("p");
        var old=Q("p",Addr,Im(In(p,C("material",t)),Eqn(C("y",p),C("x",p))));
        var fresh=Q("p",Addr,Im(In(p,C("material",G(t))),Im(Seq(Neg,Sp,P(In(p,C("material",t)))),Eqn(C("y",p),D(0)))));
        var trace=Eqn(C("nativeRun",t,l,n,x,C("calls",t)),C("some",C("tuple",G(t),m,j,y)));
        return Q("t",Source,Im(C("D",t),Bind(["l","n","x"],[C("RawMap"),Zed,Val],Ex("m",C("RawMap"),Ex("j",Zed,Ex("y",Val,Ands(trace,old,fresh)))))));
    }
    private static Formula LiftLaw() {
        var l=V("l");var r=V("r");var b=V("b");var x=V("x");
        return Bind(["l","r","b","x"],[Source,Source,C("Bool"),Val],Im(Eqn(C("x",C("empty")),D(0)),
            Eqn(C("update",C("mul",l,r),C("lift",b,x)),C("lift",b,C("update",C("if",b,r,l),x)))));
    }
}
