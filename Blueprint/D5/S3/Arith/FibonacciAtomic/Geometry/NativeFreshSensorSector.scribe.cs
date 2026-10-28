using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeFreshSensorSectorDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorSector.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six actual ambient pair actions imply the exact period and higher-power identities.", H("Native ambient beta cherry sectors"), Blocks(
        R("attained_actions", "All six ambient actions", Actions(), "For a literal original beta cherry at address p, vector(p,z) is the difference of coordinate vectors at pLz and pRz. The constants empty, L, R, LL, LR and LLL mean the corresponding lists of false and true. B is adjacency of grown(t), computed from its actual material and neighbor lists. Each equality is an equality of fields at every address. A complete local calculation includes the common parent, where the two owner contributions cancel. The zero-root transport theorem carries the calculation through an arbitrary native context, including every exterior coordinate."),
        R("attained_powers", "Period two and exact higher powers", Powers(), "Write a=vector(p,empty), b=vector(p,L), c=vector(p,LL), d=vector(p,LLL), e=vector(p,R), f=vector(p,LR), and h=(a-c)/2. All scalars are rational. These identities use the six proved native actions and linearity of the actual neighbor sum. The iterate exponents are literal natural numbers; no finite-depth approximation is involved."))));
    private static DocumentBlock R(string n, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create("nativefreshsensorsector-"+n.Replace("_","")), DeclarationHandle.Create(Prefix+n),
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

    private static Formula Vec(Formula p,string z)=>C("vector",p,C(z));
    private static Formula B(Formula t,Formula x)=>C("adjacency",G(t),x);
    private static Formula PowB(Formula t,int n,Formula x)=>C("iterate",C("adjacency",G(t)),D(n),x);
    private static Formula Scope(Formula f)=>Bind(["t","p"],[Source,Addr],Im(Eqn(C("subtree",V("p"),V("t")),C("some",C("mul",C("beta"),C("beta")))),f));
    private static Formula Actions() { var t=V("t");var p=V("p");var a=Vec(p,"empty");var b=Vec(p,"L");var c=Vec(p,"LL");var d=Vec(p,"LLL");var e=Vec(p,"R");var f=Vec(p,"LR");
        return Scope(Ands(Eqn(B(t,a),Add(b,e)),Eqn(B(t,b),Add(Add(a,c),f)),Eqn(B(t,c),Add(b,d)),Eqn(B(t,d),c),Eqn(B(t,e),a),Eqn(B(t,f),b))); }
    private static Formula Powers() {var t=V("t");var p=V("p");var a=Vec(p,"empty");var c=Vec(p,"LL");var d=Vec(p,"LLL");var e=Vec(p,"R");var f=Vec(p,"LR");var h=C("half",p);
        return Scope(Ands(Eqn(B(t,h),Half(Sub(e,d))),Eqn(B(t,B(t,h)),h),Eqn(PowB(t,2,a),Add(Add(Scale(2,a),c),f)),Eqn(PowB(t,2,f),Add(Add(a,c),f)),Eqn(PowB(t,4,a),Add(Add(Scale(6,a),Scale(5,c)),Scale(4,f))))); }
}
