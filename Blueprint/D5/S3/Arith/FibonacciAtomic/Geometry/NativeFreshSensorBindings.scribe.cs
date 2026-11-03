using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;
internal sealed class NativeFreshSensorBindingsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every inherited and allocated raw label follows the actual guarded native run.", H("Exact native raw destinations"), Blocks(
        Describe.Lean(DescribeId.Create("nativefreshsensorbindings-rawbindings"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorBindings.raw_bindings"),
            H("All integer bindings of the same successful execution"), StatementSource.FromAuthor(Raw()), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("RawMap is the actual integer-to-terminal address table used by nativeRun. The integer next is the next fresh identifier, above every authentic original identifier. Inherited follows alpha to LL and beta to LLL, with original branch prefixes unchanged. Fresh lists alpha R and beta R then LR, in allocation order under the fixed left-to-right original-leaf traversal. The theorem proves every old binding below next and every newly allocated integer destination, and the final next integer. At beta, R and LR are distinct addresses and receive different successive integers. No numerical call or pre-growth Tick occurs. Authentic original completeness, genuine grants, framing and physical conformance remain installation premises."))), DescribeRole.Theorem))));
    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Q(string n, Formula t, Formula f) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula A(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Im(Formula x, Formula y) => Seq(P(x), Sp, Rightarrow, Sp, P(y));
    private static Formula In(Formula x, Formula y) => Seq(x, Sp, InMacro, Sp, y);
    private static Formula Add(Formula x, Formula y) => Seq(P(x), Sp, Plus, Sp, P(y));
    private static Formula Bind(string[] ns, Formula[] ts, Formula f) { for(int i=ns.Length-1;i>=0;--i) f=Q(ns[i],ts[i],f); return f; }
    private static Formula Ands(params Formula[] fs) { var f=fs[^1];for(int i=fs.Length-2;i>=0;--i)f=A(fs[i],f);return f; }
    private static Formula Source => C("Source");
    private static Formula Val => C("Value");
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Zed => Seq(Mathbb, Grp(V("Z")));

    private static Formula Raw() {var t=V("t");var u=V("u");var l=V("labels");var r=V("result");var n=V("next");var m=V("after");var x=V("x");var y=V("y");var i=V("i");var j=V("j");var f=C("fresh",t);
        return Bind(["t","u","labels","result","next","after","x","y"],[Source,Source,C("RawMap"),C("RawMap"),Zed,Zed,Val,Val],
            Im(Eqn(C("nativeRun",t,l,n,x,C("calls",t)),C("some",C("tuple",u,r,m,y))),Ands(
                Eqn(m,Add(n,C("length",f))),
                Q("i",Zed,Im(C("lt",i,n),Im(In(C("apply",l,i),C("terminals",t)),Eqn(C("apply",r,i),C("inherited",t,C("apply",l,i)))))),
                Q("j",Nat,Im(C("lt",j,C("length",f)),Eqn(C("apply",r,Add(n,j)),C("get",f,j)))))));
    }
}
