using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeFreshSensorFamilyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorFamily.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Disjoint original beta cherries carry independent rational period-two sectors invisible at every designated observation time.", H("Independent persistent native sectors"), Blocks(
        R("designated_support", "Terminal and designated support on arbitrary native contexts", Support(), "For every original beta cherry, half vanishes at all current terminals and all designated sensors; its native adjacency update also vanishes at every designated sensor. Embedding through the actual original context proves these assertions for every ambient terminal and sensor."),
        R("persistent_family", "Every rational parameter and every natural time", Family(), "Cherries(t,k) records k literal beta cherries in the original finite Source and disjoint full address cones: for distinct indices i,j, root(i)++p differs from root(j)++q for every pair of suffixes p,q. This is disjointness of native logical cones. H(theta) is the finite sum of theta(i) times half(root(i)). Its coordinate at root(i)L is theta(i)/2, proving injectivity over all rational parameters. Each summand and its first update vanish at every designated sensor. Period two proves invisibility for every natural time, including zero. Every current terminal of grown(t) has zero value in H(theta). The first update may be visible at nondesignated terminals; designated blindness does not assert full-service equality. The native fresh-zero entrance generally differs from H(theta), and no acquisition of this sector is asserted."))));
    private static DocumentBlock R(string n, string title, Formula f, string text) =>
        Describe.Lean(DescribeId.Create("nativefreshsensorfamily-"+n.Replace("_","")), DeclarationHandle.Create(Prefix+n),
            H(title), StatementSource.FromAuthor(f), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Q(string n, Formula t, Formula f) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula A(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Im(Formula x, Formula y) => Seq(P(x), Sp, Rightarrow, Sp, P(y));
    private static Formula In(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Bind(string[] ns, Formula[] ts, Formula f) { for(int i=ns.Length-1;i>=0;--i) f=Q(ns[i],ts[i],f); return f; }
    private static Formula Ands(params Formula[] fs) { var f=fs[^1];for(int i=fs.Length-2;i>=0;--i)f=A(fs[i],f);return f; }
    private static Formula Source => C("Source");
    private static Formula Addr => C("Address");
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Rat => Seq(Mathbb, Grp(V("Q")));
    private static Formula G(Formula t) => C("grown",t);

    private static Formula Support() { var t=V("t");var p=V("p");var q=V("q");var h=C("half",p);
        return Bind(["t","p"],[Source,Addr],Im(Eqn(C("subtree",p,t),C("some",C("mul",C("beta"),C("beta")))),Ands(
            Q("q",Addr,Im(In(q,C("terminals",G(t))),Eqn(C("coordinate",h,q),D(0)))),
            Q("q",Addr,Im(In(q,C("sensors",t)),Eqn(C("coordinate",h,q),D(0)))),
            Q("q",Addr,Im(In(q,C("sensors",t)),Eqn(C("coordinate",C("adjacency",G(t),h),q),D(0))))))); }
    private static Formula Family() {
        var t=V("t");var k=V("k");var ch=V("ch");var th=V("theta");var j=V("j");var q=V("q");
        var param=Seq(C("Fin",k),Sp,To,Sp,Rat);var h=C("H",ch,th);var b=C("adjacency",G(t));
        return Bind(["t","k","ch"],[Source,Nat,C("Cherries",t,k)],Ands(
            C("Injective",C("H",ch)),Q("theta",param,Eqn(C("apply",b,C("apply",b,h)),h)),
            Bind(["theta","j","q"],[param,Nat,Addr],Im(In(q,C("sensors",t)),Eqn(C("coordinate",C("iterate",b,j,h),q),D(0)))),
            Bind(["theta","q"],[param,Addr],Im(In(q,C("terminals",G(t))),Eqn(C("coordinate",h,q),D(0))))));
    }
}
