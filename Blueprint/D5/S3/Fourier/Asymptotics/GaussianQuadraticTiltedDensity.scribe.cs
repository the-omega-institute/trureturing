using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics;

internal sealed class GaussianQuadraticTiltedDensityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A cardinal core of small variances controls the physical tilted energy density on compact intervals.",
        H("Gaussian Quadratic Tilted Density"),
        Blocks(Describe.Lean(
            DescribeId.Create("gaussian-quadratic-tilted-density"),
            DeclarationHandle.Create("D5/S3/Fourier/Asymptotics/GaussianQuadraticTiltedDensity.result"),
            H("Uniform compact lower bound for the actual convolution"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Fix real constants kappa, K and R with 0<kappa<=1, K>=1 and R>=0. There are positive deltaZero and c, with deltaZero<=1, chosen before every finite array. For each finite decidable index type J, choose finite subsets H and Core, real arrays v and e, and real delta, sigma, alpha and t. Require 0<delta<=deltaZero, 0<sigma<=1 and 1<=alpha<=2. Every v(j) is nonnegative and is positive on H. Set V=sum v(j) and d(j)=1-2t v(j)/alpha. Require kappa<=V<=K and v(j)<=K delta for every index.")),
                Paragraph(Text("Require Core to be contained in H, its cardinality to be at least kappa/delta, and v(j)>=kappa delta on Core. Require card(H)<=K delta^(-4), abs(e(j))<=K sqrt(v(j)) delta^2, and kappa<=d(j)<=K at every index, including outside H. The signed tilt satisfies abs(t)<=K/delta and the exact full-array saddle equation sum v(j)/(alpha d(j))+sum e(j)^2/d(j)^2+delta sigma^2 t/alpha=V. The omitted mass sum over J outside H of v(j)+e(j)^2 is at most delta^2.")),
                Paragraph(Text("Put nu=delta sigma^2/alpha and let P be the product standard Gaussian measure on the real coordinates indexed by H. Define Xt(z)(j)=sqrt(v(j)/(alpha d(j)))z(j)-e(j)/d(j) and E(x)=sum x(j)^2. At h=V+sqrt(delta)y, define gt to be the integral under P of gaussianPDFReal(nu t,nu.toNNReal,h-E(Xt(z))). For every real y with abs(y)<=R, gt is at least c/sqrt(delta). Sigma has no uniform positive lower bound.")),
                Paragraph(Text("Write w(j)=v(j)/(alpha d(j)), m(j)=-e(j)/d(j), W=2 sum over H of w(j)^2+4 sum over H of w(j)m(j)^2+nu, and tau=sum outside H of w(j)+m(j)^2. With L=kappa^3/(2K^2) and U=1+2K^2/kappa^2+4K^4/kappa^3, the physical variance lies between L delta and U delta. The full saddle gives mean mu=V-tau and 0<=tau<=kappa^(-2)delta^2. Normalize a(j)=w(j)/sqrt(W), b(j)=2m(j)sqrt(w(j))/sqrt(W) and gamma=sqrt(nu)/sqrt(W); then 2 sum a(j)^2+sum b(j)^2+gamma^2=1.")),
                Paragraph(Text("The core supplies the integrable Fourier envelope F(xi)=(1+cF xi^2)^(-8), with A=kappa^2/(4K^2 U) and cF=A kappa/8. For M=K sqrt(delta)/(kappa sqrt(L)), the central logarithmic remainder and the noncentral reciprocal remainder in the exact scalar characteristic function give local error at most 3M abs(xi)^3 exp(3M abs(xi)^3). If n>=7 and M<=1/(n+1), use that estimate only for abs(xi)<=(n+1)/4. Outside this cutoff its n-dependent bound is at least 3, whereas 2F(xi)+exp(-xi^2/2)<=3. The error is therefore globally bounded by the minimum of these two envelopes.")),
                Paragraph(Text("Dominated convergence makes the integral of that minimum arbitrarily small before the arrays are chosen. Set X=(R+kappa^(-2))/sqrt(L), eta=exp(-X^2/2)/sqrt(2pi), choose n with integral at most pi eta, and take deltaZero=min(1,kappa/32,1/(MZero^2(n+1)^2)) and c=eta/(2sqrt(U)), where MZero=K/(kappa sqrt(L)). Gaussian convolution inversion uses nu>0, noise mean nu t and the substitution -xi/(2pi sqrt(W)), whose absolute Jacobian is 1/(2pi sqrt(W)). Its mean phases cancel at mu. The resulting density error is at most eta/2; abs(y)<=R places the target within X standard deviations and yields the stated lower bound."))),
            DescribeRole.Theorem))));

    private static Formula R => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula And(params Formula[] xs) => xs.Aggregate((a, b) => new Formula.Logic(a, FormulaLogicOperator.And, b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(string n, Formula t, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(n), t)], b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.BindMany(FormulaQuantifier.Exists,
        [new Formula.BoundVariable(FormulaIdentifier.Create(n), t)], b);
    private static Formula Le(Formula a, Formula b) => F.Seq(a, F.Le, F.Sp, b);
    private static Formula Lt(Formula a, Formula b) => F.Seq(a, F.Lt, F.Sp, b);
    private static Formula Eq(Formula a, Formula b) => F.Seq(a, F.Eq, F.Sp, b);
    private static Formula Add(params Formula[] a) => a.Aggregate((x, y) => F.Grp(F.Seq(x, F.Plus, y)));
    private static Formula Sub(Formula a, Formula b) => F.Grp(F.Seq(a, F.Minus, b));
    private static Formula Mul(Formula a, Formula b) => Multiply(a, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Sq(Formula a) => new Formula.Power(a, F.D(2));
    private static Formula Abs(Formula a) => new Formula.Absolute(a);
    private static Formula Lam(string n, Formula t, Formula b) => F.Seq(F.Open, F.Id(n), F.Colon, t, F.Mapsto, F.Sp, b, F.Close);
    private static Formula At(Formula f, Formula x) => Call("apply", f, x);
    private static Formula TheoremFormula()
    {
        Formula k=F.Id("kappa"), K=F.Id("K"), r=F.Id("R"), dz=F.Id("deltaZero"), c=F.Id("c"),
            J=F.Id("J"), Hs=F.Id("H"), core=F.Id("Core"), v=F.Id("v"), e=F.Id("e"),
            de=F.Id("delta"), sig=F.Id("sigma"), al=F.Id("alpha"), t=F.Id("t"), j=F.Id("j"), y=F.Id("y");
        Formula zero=F.D(0), one=F.D(1), two=F.D(2), vj=At(v,j), ej=At(e,j);
        Formula d(Formula i) => Sub(one,Div(Mul(Mul(two,t),At(v,i)),al));
        Formula sum(Formula s, Formula body) => Call("sum",s,Lam("j",J,body));
        Formula V=sum(Call("univ",J),vj), nu=Div(Mul(de,Sq(sig)),al);
        Formula indexH=Call("Subtype",Hs), coords=Call("Function",indexH,R);
        Formula z=F.Id("z"), x=F.Id("x"), i=F.Id("i"), ji=Call("val",i);
        Formula xt=Lam("z",coords,Lam("i",indexH,
            Sub(Mul(Call("sqrt",Div(At(v,ji),Mul(al,d(ji)))),At(z,i)),Div(At(e,ji),d(ji)))));
        Formula energy=Lam("x",coords,Call("sum",Call("univ",indexH),Lam("i",indexH,Sq(At(x,i)))));
        Formula P=Call("pi",Lam("i",indexH,Call("gaussianReal",zero,one)));
        Formula target=Add(V,Mul(Call("sqrt",de),y));
        Formula density=Call("integral",P,Lam("z",coords,
            Call("gaussianPDFReal",Mul(nu,t),Call("toNNReal",nu),Sub(target,At(energy,At(xt,z))))));
        Formula dj=d(j);
        Formula hyp=And(Lt(zero,de),Le(de,dz),Lt(zero,sig),Le(sig,one),Le(one,al),Le(al,two),
            All("j",J,Le(zero,vj)),All("j",J,Imp(Call("member",j,Hs),Lt(zero,vj))),
            Le(k,V),Le(V,K),All("j",J,Le(vj,Mul(K,de))),Call("subset",core,Hs),
            Le(Div(k,de),Call("card",core)),All("j",J,Imp(Call("member",j,core),Le(Mul(k,de),vj))),
            Le(Call("card",Hs),Mul(K,new Formula.Power(de,F.Grp(F.Seq(F.Minus,F.D(4)))))),
            All("j",J,Le(Abs(ej),Mul(Mul(K,Call("sqrt",vj)),Sq(de)))),
            All("j",J,And(Le(k,dj),Le(dj,K))),Le(Abs(t),Div(K,de)),
            Eq(Add(sum(Call("univ",J),Div(vj,Mul(al,dj))),sum(Call("univ",J),Div(Sq(ej),Sq(dj))),Mul(nu,t)),V),
            Le(sum(Call("sdiff",Call("univ",J),Hs),Add(vj,Sq(ej))),Sq(de)));
        Formula body=All("y",R,Imp(Le(Abs(y),r),Le(Div(c,Call("sqrt",de)),density)));
        body=Imp(hyp,body);
        body=All("t",R,body); body=All("alpha",R,body); body=All("sigma",R,body); body=All("delta",R,body);
        body=All("e",Call("Function",J,R),body); body=All("v",Call("Function",J,R),body);
        body=All("Core",Call("Finset",J),body); body=All("H",Call("Finset",J),body);
        body=All("J",F.Id("FiniteDecidableType"),body);
        body=Ex("deltaZero",R,Ex("c",R,And(Lt(zero,dz),Le(dz,one),Lt(zero,c),body)));
        body=Imp(And(Lt(zero,k),Le(k,one),Le(one,K),Le(zero,r)),body);
        return F.Disp(All("kappa",R,All("K",R,All("R",R,body))));
    }
}
