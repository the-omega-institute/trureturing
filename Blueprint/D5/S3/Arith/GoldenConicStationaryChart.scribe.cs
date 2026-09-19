using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenConicStationaryChartDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Arith/GoldenConicStationaryChart.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An invertible golden norm chart retains the quadratic normal phase at odd precision.",
        H("Golden Norm Charts and the Exact Stationary Phase"),
        Blocks(
            Paragraph(Text("The carrier is the existing GoldenApparition.GoldenMod M. "
                + "Coordinates and coefficients belong to ZMod M, even when M is composite. "
                + "No field instance is imposed on that ring. The inverse certificates "
                + "2*half=1 and normForm(z)*invc=1 are explicit hypotheses.")),
            Describe.Lean(DescribeId.Create("golden-conic-norm"),
                DeclarationHandle.Create(Owner + "normForm"), H("Actual modular golden norm"),
                StatementSource.FromAuthor(NormFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("normForm(z)=z.a^2+z.a*z.b-z.b^2, the reduction "
                    + "of the original integer golden norm in its existing coordinate basis."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-conic-tangent"),
                DeclarationHandle.Create(Owner + "tangent"), H("The specified tangent direction"),
                StatementSource.FromAuthor(TangentFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The tangent is (z.a-2*z.b,-2*z.a-z.b). It is "
                    + "orthogonal to the norm gradient and has norm -5*normForm(z)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-conic-chart"),
                DeclarationHandle.Create(Owner + "chart"), H("The chart with a certified inverse"),
                StatementSource.FromAuthor(ChartFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("chart(z,t,d)=d*((1+5*t^2)*z+2*t*tangent(z)) "
                    + "coordinatewise. The theorem requires d*(1-5*t^2)=1 when invoking "
                    + "this inverse. No division by a nonunit is performed."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-conic-radial"),
                DeclarationHandle.Create(Owner + "radial"), H("Radial coordinate in the moving basis"),
                StatementSource.FromAuthor(RadialFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With the stated inverse certificates, radial is "
                    + "the coefficient A of z when w=A*z+B*tangent(z)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-conic-transverse"),
                DeclarationHandle.Create(Owner + "transverse"), H("Tangential coordinate in the moving basis"),
                StatementSource.FromAuthor(TransverseFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("transverse is the coefficient B in the same moving "
                    + "basis. Its determinant denominator is the certified unit 2*normForm(z)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("golden-conic-exact-chart-phase"),
                DeclarationHandle.Create(Owner + "result"), H("Norm, unique inverse, and quadratic phase"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every modulus M and unit-norm point z with the "
                        + "two inverse certificates, every valid chart point has exactly "
                        + "the original norm. A normal frequency lambda*gradient(Q)(z) "
                        + "has phase 2*lambda*Q(z)+20*lambda*Q(z)*t^2*d.")),
                    Paragraph(Text("Conversely, for every w with the same norm, put "
                        + "A=radial(z,w,half,invc) and B=transverse(z,w,half,invc). "
                        + "If e*(1+A)=1, the explicitly recovered parameter B*e and "
                        + "denominator inverse (1+A)*half give w. Any other chart "
                        + "representation has that same parameter. In a ball modulo "
                        + "p^h about z, A is one and B is zero modulo p^h, so this "
                        + "inverse covers the entire ball when p is odd.")),
                    Paragraph(Text("If t^3=0, the exact point is (1+10*t^2)*z+2*t*tangent(z), "
                        + "and its normal phase is 2*lambda*Q(z)+20*lambda*Q(z)*t^2. "
                        + "At modulus p^(2*r+1), a parameter divisible by p^r has "
                        + "cube zero for r>=1, while its square can remain nonzero. "
                        + "This is the quadratic term in the odd-precision Gauss sum.")),
                    Paragraph(Text("The proof constructs the basis inverse, derives "
                        + "A^2-5*B^2=1 from the actual norm, and verifies the inverse "
                        + "and phase by ring identities. The analytic character-sum "
                        + "evaluation is an ordinary theorem in the existing theory "
                        + "note, not a further formal conclusion of this declaration."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Num(int n) => n < 10 ? D(n) : Seq(n.ToString().Select(c => D(c-'0')).ToArray());
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), a);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(x, Num(n));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula All(string x, Formula type, Formula body) => Seq(Forall,Sp,V(x),Sp,InMacro,Sp,type,Comma,Sp,body);
    private static Formula And(params Formula[] args)
    {
        var result=args[^1];
        for(var j=args.Length-2;j>=0;--j) result=C("And",args[j],result);
        return result;
    }
    private static Formula Imp(Formula x, Formula y) => C("Implies",x,y);
    private static Formula R() => C("ZMod",V("M"));
    private static Formula Z() => C("GoldenMod",V("M"));
    private static Formula X(Formula z) => C("a",z);
    private static Formula Y(Formula z) => C("b",z);
    private static Formula N(Formula z) => C("normForm",z);
    private static Formula Tan(Formula z) => C("tangent",z);
    private static Formula Pt(Formula a, Formula b) => C("GoldenMod.mk",a,b);
    private static Formula Ch(Formula t, Formula d) => C("chart",V("z"),t,d);
    private static Formula A() => C("radial",V("z"),V("w"),V("half"),V("invc"));
    private static Formula B() => C("transverse",V("z"),V("w"),V("half"),V("invc"));
    private static Formula Den(Formula t, Formula d) => Eqn(Mul(d,Sub(Num(1),Mul(Num(5),Pow(t,2)))),Num(1));
    private static Formula Phase(Formula w) => Add(Mul(Mul(V("lam"),Add(Mul(Num(2),X(V("z"))),Y(V("z")))),X(w)),
        Mul(Mul(V("lam"),Sub(X(V("z")),Mul(Num(2),Y(V("z"))))),Y(w)));
    private static Formula PhaseBase() => Mul(Mul(Num(2),V("lam")),N(V("z")));
    private static Formula Correction(Formula t) => Mul(Mul(Mul(Num(20),V("lam")),N(V("z"))),Pow(t,2));
    private static Formula NormFormula() => Disp(All("z",Z(),Eqn(N(V("z")),Sub(Add(Pow(X(V("z")),2),Mul(X(V("z")),Y(V("z")))),Pow(Y(V("z")),2)))));
    private static Formula TangentFormula() => Disp(All("z",Z(),Eqn(Tan(V("z")),Pt(Sub(X(V("z")),Mul(Num(2),Y(V("z")))),C("neg",Add(Mul(Num(2),X(V("z"))),Y(V("z"))))))));
    private static Formula ChartFormula()
    {
        Formula Co(Formula z,Formula v) => Mul(V("d"),Add(Mul(Add(Num(1),Mul(Num(5),Pow(V("t"),2))),z),Mul(Mul(Num(2),V("t")),v)));
        return Disp(All("z",Z(),All("t",R(),All("d",R(),Eqn(Ch(V("t"),V("d")),Pt(Co(X(V("z")),X(Tan(V("z")))),Co(Y(V("z")),Y(Tan(V("z"))))))))));
    }
    private static Formula RadialFormula() => Disp(All("z",Z(),All("w",Z(),All("half",R(),All("invc",R(),Eqn(A(),
        Mul(Mul(V("half"),V("invc")),Add(Mul(Add(Mul(Num(2),X(V("z"))),Y(V("z"))),X(V("w"))),Mul(Sub(X(V("z")),Mul(Num(2),Y(V("z")))),Y(V("w")))))))))));
    private static Formula TransverseFormula() => Disp(All("z",Z(),All("w",Z(),All("half",R(),All("invc",R(),Eqn(B(),
        Mul(Mul(V("half"),V("invc")),Sub(Mul(Y(V("z")),X(V("w"))),Mul(X(V("z")),Y(V("w")))))))))));
    private static Formula ResultFormula()
    {
        var t=V("t");var d=V("d");var e=V("e");
        var forward=All("t",R(),All("d",R(),Imp(Den(t,d),And(Eqn(N(Ch(t,d)),N(V("z"))),
            All("lam",R(),Eqn(Phase(Ch(t,d)),Add(PhaseBase(),Mul(Correction(t),d))))))));
        var t0=Mul(B(),e);var d0=Mul(Add(Num(1),A()),V("half"));
        var inverse=All("w",Z(),Imp(Eqn(N(V("w")),N(V("z"))),All("e",R(),Imp(Eqn(Mul(e,Add(Num(1),A())),Num(1)),
            And(Den(t0,d0),Eqn(Ch(t0,d0),V("w")),All("t",R(),All("d",R(),Imp(Den(t,d),Imp(Eqn(Ch(t,d),V("w")),Eqn(t,t0))))))))));
        var jd=Add(Num(1),Mul(Num(5),Pow(t,2)));
        Formula JC(Formula z,Formula v) => Add(Mul(Add(Num(1),Mul(Num(10),Pow(t,2))),z),Mul(Mul(Num(2),t),v));
        var jet=All("t",R(),Imp(Eqn(Pow(t,3),Num(0)),And(Eqn(Ch(t,jd),Pt(JC(X(V("z")),X(Tan(V("z")))),JC(Y(V("z")),Y(Tan(V("z")))))),
            Eqn(N(Ch(t,jd)),N(V("z"))),All("lam",R(),Eqn(Phase(Ch(t,jd)),Add(PhaseBase(),Correction(t)))))));
        var assumptions=And(Eqn(Mul(Num(2),V("half")),Num(1)),Eqn(Mul(N(V("z")),V("invc")),Num(1)));
        return Disp(All("M",Seq(Mathbb,Grp(V("N"))),All("z",Z(),All("half",R(),All("invc",R(),Imp(assumptions,And(forward,inverse,jet)))))));
    }
}
