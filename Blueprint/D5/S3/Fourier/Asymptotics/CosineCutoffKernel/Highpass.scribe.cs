using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Asymptotics.CosineCutoffKernel;

internal sealed class HighpassDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Fourier/Asymptotics/CosineCutoffKernel/Highpass.";
    private const string Cutoff = "D5/S3/Fourier/Asymptotics/CosineCutoffKernel.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive cosine-integral kernel is the actual L2 limit of the finite cutoffs. Its ordinary convolution and original Gaussian weighted integral operator inherit the high-pass bound.",
        H("Actual cosine-integral high-pass operators"),
        Blocks(
            Paragraph(Text("Write q(c,x)=2 Ci(c|x|), where Ci is the existing sine-tail cosine integral. The totalized origin value is immaterial in Lebesgue L2 and in the Gaussian product measure."),
                Math(Equal(Call("q", Id("c"), Id("x")), Multiply(F.D(2), Call("Ci", Multiply(Id("c"), new Formula.Absolute(Id("x"))))))),
                Ref(Module + "highpassKernel"), Ref("D5/S3/Fourier/Asymptotics/CosineIntegralLattice.cosineIntegral")),
            Describe.Lean(DescribeId.Create("positive-ci-exact-l2-cutoff-limit"),
                DeclarationHandle.Create(Module + "highpass_limit"),
                H("Exact cutoff error and every real cutoff filter"),
                StatementSource.FromAuthor(LimitFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every c>0, q(c) is measurable and belongs to real Lebesgue L2. For every N>=c and every MemLp witness for the actual kernel(c,N), the squared L2 error is 4*pi/N. Every filter of real upper cutoffs tending to infinity gives L2 convergence, without requiring a nontrivial filter.")),
                    Paragraph(Text("The finite interval cancellation uses the existing positive Euler normalization. Away from x=0, kernel(c,N,x)=q(c,x)-q(N,x). The exact Gram integral at the scale N gives the squared error. At N=c the finite kernel is zero; closed frequency endpoints remain qualified almost everywhere."),
                        Ref("D5/S3/Fourier/Asymptotics/CosineNormalizedRemainder.positive_normalization"),
                        Ref("D5/S3/Fourier/Asymptotics/CosineIntegralGram.result"), Ref(Cutoff + "result")),
                    Paragraph(Text("This lemma is consumed by the actual high-pass convolution construction and by Gaussian kernel convergence. Its direct reuse and normalization steps receive no separate mathematical-content credit."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ci-unweighted-convolution"),
                DeclarationHandle.Create(Module + "actual_highpass_convolution"),
                H("Ordinary convolution on the full complex and real L2 spaces"),
                StatementSource.FromAuthor(ConvolutionFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("HC=Lp(C,2,volume) and HR=Lp(R,2,volume). The complex convolution rows are integrable for every L2 input and every real x. One bounded complex operator represents these ordinary integrals almost everywhere. Its real restriction is obtained using the ofReal and real-part maps and has the same bound 2*pi/c.")),
                    Paragraph(Text("The finite operators are Cauchy in operator norm by the existing cutoff tail estimate. Their L2 kernel limit identifies the ordinary convolution integral through the continuous bilinear L2 pairing and translation-reflection isometry. An almost-everywhere convergent subsequence of each operator output identifies its L2 representative with that pointwise integral limit."),
                        Ref(Cutoff + "actual_cutoff_convolution"), Ref(Cutoff + "pair"), Ref(Cutoff + "pair_eq"), Ref(Cutoff + "product_integrable")),
                    Paragraph(Text("No absolute integrability of q is assumed. The pinned forward Fourier convention is exp(-2*pi*i*x*xi); the finite physical cutoff c is therefore at c/(2*pi) in xi, or at c in the original variable zeta=2*pi*xi."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-ci-original-gaussian-operator"),
                DeclarationHandle.Create(Module + "actual_highpass_operator"),
                H("The actual weighted operator, onto density isometry, and cutoff limit"),
                StatementSource.FromAuthor(WeightedFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every r,alpha with 0<r<1, a=(1+r)/2, b=(1-r)/2, c0=1/(4*pi*sqrt(a*b)), kappa=1/a+alpha^2/b, rho(x)=c0*exp(-kappa*x^2/2), and mu=volume.withDensity(ENNReal.ofReal(rho)). This is the finite, unnormalized original Gaussian measure.")),
                    Paragraph(Text("A is the existing continuous linear factory for the actual integral kernel operators. For every c>0 the displayed kernel K represents q(c,x-y); A(K) has that weighted integral representative and almost-everywhere integrable rows. C is the actual ordinary real convolution supplied above. U is an onto real linear isometry, with both forward density and inverse division representatives. M multiplies by sqrt(rho). The identity conjugates A(K) with U; A(K) is not defined as the sandwich.")),
                    Paragraph(Text("For every N>=c, Ks(N,hN) represents the actual finite kernel(c,N,x-y), has the same bound, and converges with A(Ks) for every real cutoff filter tending to infinity. This uses the Gaussian difference-kernel L2 estimate and the actual operator factory continuity."),
                        Ref(Cutoff + "actual_cutoff_real"), Ref(Cutoff + "actual_weighted_cutoff"),
                        Ref("D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight.gaussian_weighted_kernel"),
                        Ref("D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight.weighted_integral_operator"),
                        Ref("D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight.density_unitary"),
                        Ref("D5/S3/Fourier/Asymptotics/CosineCutoffKernel/GaussianWeight.cutoff_conjugacy")),
                    Paragraph(Text("The norm bound is c0*(2*pi/c). Substituting c=(pi/2)*exp(s+t) gives the first original operator bound for every real s,t. Scaling the actual kernel by exp((s+t)/2) and using t>=t0 gives the compact-window bound with C_I=(2*pi*c0/(pi/2))*exp(-t0/2), including singleton windows. These substitutions are exact applications. This result makes no spectral-series, covariance-asymptotic, path-convergence or completed-field mixing claim."))),
                DescribeRole.Theorem))));

    private static Formula Id(string s) => F.Id(s);
    private static Formula R => F.Seq(F.Mathbb, F.Grp(Id("R")));
    private static Formula C => F.Seq(F.Mathbb, F.Grp(Id("C")));
    private static Formula V => Id("volume");
    private static Formula HR => Call("Lp", R, F.D(2), V);
    private static Formula HC => Call("Lp", C, F.D(2), V);
    private static Formula Q(Formula c) => Call("highpassKernel", c);
    private static Formula Cut(Formula c, Formula n) => Call("kernel", c, n);
    private static Formula All(string n, Formula t, Formula b) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(n), t)], b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.BindMany(FormulaQuantifier.Exists,
        [new Formula.BoundVariable(FormulaIdentifier.Create(n), t)], b);
    private static Formula Arrow(Formula a, Formula b) => F.Grp(F.Seq(a, F.To, F.Sp, b));
    private static Formula Lam(string n, Formula t, Formula b) => F.Seq(F.Open, Id(n), F.Colon, F.Sp, t, F.Sp, F.Mapsto, F.Sp, b, F.Close);
    private static Formula App(Formula f, params Formula[] args)
    {
        Formula[] a=new Formula[args.Length+1];
        a[0]=f;
        for (int i=0; i<args.Length; i++) a[i+1]=args[i];
        return Call("apply",a);
    }
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Pos(Formula a) => new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, a);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(params Formula[] a)
    {
        Formula r = a[^1];
        for (int i=a.Length-2; i>=0; i--) r=new Formula.Logic(a[i], FormulaLogicOperator.And, r);
        return r;
    }
    private static Formula L2(Formula f) => Call("MemLp", f, F.D(2), V);
    private static Formula Clm(Formula field, Formula a, Formula b) => Call("ContinuousLinearMap", field, a, b);
    private static Formula Norm(Formula a) => Call("norm", a);
    private static Formula AE(Formula a, Formula b, Formula m) => Call("AEEq", a, b, m);
    private static Formula B(Formula c) => new Formula.Fraction(Multiply(F.D(2), F.Pi), c);
    private static Formula Integral(Formula f, Formula m) => Call("integral", f, m);
    private static Formula Conv(Formula q, Formula f, Formula m) => Lam("x", R,
        Integral(Lam("y", R, Multiply(App(q, Subtract(Id("x"), Id("y"))), App(f, Id("y")))), m));
    private static Formula Tends(Formula f, Formula l, Formula x) => Call("Tendsto", f, l, Call("nhds", x));
    private static Formula LimitFormula()
    {
        Formula c=Id("c"), n=Id("N"), hq=Id("hq"), hn=Id("hNq"), l=Id("l"), ns=Id("Ns");
        Formula qt=Call("toLp", hq,Q(c));
        Formula error=Equal(Call("square", Norm(Subtract(Call("toLp",hn,Cut(c,n)),qt))),
            new Formula.Fraction(Multiply(F.D(4),F.Pi),n));
        Formula filter=All("iota",Id("Type"),All("l",Call("Filter",Id("iota")),
            All("Ns",Arrow(Id("iota"),R),All("hNs",All("i",Id("iota"),Le(c,App(ns,Id("i")))),
            All("hcuts",All("i",Id("iota"),L2(Cut(c,App(ns,Id("i"))))),
                Imp(Call("Tendsto",ns,l,Id("atTop")),Tends(Lam("i",Id("iota"),
                    Call("toLp",App(Id("hcuts"),Id("i")),Cut(c,App(ns,Id("i"))))),l,qt)))))));
        return F.Disp(All("c",R,Imp(Pos(c),And(Call("Measurable",Q(c)),
            Ex("hq",L2(Q(c)),And(All("N",R,Imp(Le(c,n),All("hNq",L2(Cut(c,n)),error))),filter))))));
    }
    private static Formula ConvolutionFormula()
    {
        Formula c=Id("c"), op=Id("C"), cr=Id("Cr"), f=Id("f"), x=Id("x");
        Formula qc=Lam("z",R,Call("ofReal",App(Q(c),Id("z"))));
        Formula integ=All("f",HC,All("x",R,Call("Integrable",Lam("y",R,
            Multiply(App(qc,Subtract(x,Id("y"))),App(f,Id("y")))),V)));
        Formula real=Ex("Cr",Clm(R,HR,HR),And(All("f",HR,AE(Call("coeFn",App(cr,f)),Conv(Q(c),f,V),V)),Le(Norm(cr),B(c))));
        return F.Disp(All("c",R,Imp(Pos(c),Ex("C",Clm(C,HC,HC),And(integ,
            All("f",HC,AE(Call("coeFn",App(op,f)),Conv(qc,f,V),V)),Le(Norm(op),B(c)),real)))));
    }
    private static Formula WeightedFormula()
    {
        Formula r=Id("r"), alpha=Id("alpha"), c=Id("c"), n=Id("N"), hn=Id("hN"),
            k=Id("K"), aop=Id("A"), cop=Id("C"), f=Id("f"), h=Id("h"), u=Id("U"), m=Id("M"), ks=Id("Ks"), l=Id("l"), ns=Id("Ns");
        Formula a=new Formula.Fraction(Add(F.D(1),r),F.D(2)), b=new Formula.Fraction(Subtract(F.D(1),r),F.D(2));
        Formula c0=new Formula.Fraction(F.D(1),Multiply(Multiply(F.D(4),F.Pi),Call("sqrt",Multiply(a,b))));
        Formula kap=Add(new Formula.Fraction(F.D(1),a),new Formula.Fraction(Multiply(alpha,alpha),b));
        Formula Rho(Formula x)=>Multiply(c0,Call("exp",F.Seq(F.Minus,F.Grp(new Formula.Fraction(Multiply(kap,Multiply(x,x)),F.D(2))))));
        Formula mu=Call("withDensity",V,Lam("x",R,Call("ennrealOfReal",Rho(Id("x")))));
        Formula hk=Call("Lp",R,F.D(2),Call("prod",mu,mu)), hf=Call("Lp",R,F.D(2),mu);
        Formula raw=All("K",hk,All("f",hf,AE(Call("coeFn",App(App(aop,k),f)),Lam("x",R,
            Integral(Lam("y",R,Multiply(App(k,Call("pair",Id("x"),Id("y"))),App(f,Id("y")))),mu)),mu)));
        Formula kraw=Lam("z",Call("Product",R,R),App(Q(c),Subtract(Call("fst",Id("z")),Call("snd",Id("z")))));
        Formula uraw=All("f",hf,AE(Call("coeFn",App(u,f)),Lam("x",R,Multiply(Call("sqrt",Rho(Id("x"))),App(f,Id("x")))),V));
        Formula uinv=All("h",HR,AE(Call("coeFn",App(Call("symm",u),h)),Lam("x",R,new Formula.Fraction(App(h,Id("x")),Call("sqrt",Rho(Id("x"))))),mu));
        Formula mraw=All("h",HR,AE(Call("coeFn",App(m,h)),Lam("x",R,Multiply(Call("sqrt",Rho(Id("x"))),App(h,Id("x")))),V));
        Formula conj=Ex("U",Call("LinearIsometryEquiv",R,hf,HR),Ex("M",Clm(R,HR,HR),And(uraw,uinv,mraw,Le(Norm(m),Call("sqrt",c0)),
            Equal(Call("compose",Call("asCLM",u),Call("compose",App(aop,k),Call("asCLM",Call("symm",u)))),Call("compose",m,Call("compose",cop,m))))));
        Formula cuttype=All("N",R,Arrow(Le(c,n),hk));
        Formula cutraw=All("N",R,All("hN",Le(c,n),AE(Call("coeFn",App(ks,n,hn)),Lam("z",Call("Product",R,R),
            App(Cut(c,n),Subtract(Call("fst",Id("z")),Call("snd",Id("z"))))),Call("prod",mu,mu))));
        Formula cutbound=All("N",R,All("hN",Le(c,n),Le(Norm(App(aop,App(ks,n,hn))),Multiply(c0,B(c)))));
        Formula ki=App(ks,App(ns,Id("i")),App(Id("hNs"),Id("i")));
        Formula conv=All("iota",Id("Type"),All("l",Call("Filter",Id("iota")),All("Ns",Arrow(Id("iota"),R),
            All("hNs",All("i",Id("iota"),Le(c,App(ns,Id("i")))),Imp(Call("Tendsto",ns,l,Id("atTop")),
            And(Tends(Lam("i",Id("iota"),ki),l,k),Tends(Lam("i",Id("iota"),App(aop,ki)),l,App(aop,k))))))));
        Formula rows=All("f",hf,Call("AlmostEverywhere",mu,Lam("x",R,Call("Integrable",Lam("y",R,
            Multiply(App(Q(c),Subtract(Id("x"),Id("y"))),App(f,Id("y")))),mu))));
        Formula body=Ex("C",Clm(R,HR,HR),Ex("K",hk,And(All("f",HR,AE(Call("coeFn",App(cop,f)),Conv(Q(c),f,V),V)),Le(Norm(cop),B(c)),
            AE(Call("coeFn",k),kraw,Call("prod",mu,mu)),All("f",hf,AE(Call("coeFn",App(App(aop,k),f)),Conv(Q(c),f,mu),mu)),
            rows,Le(Norm(App(aop,k)),Multiply(c0,B(c))),conj,Ex("Ks",cuttype,And(cutraw,cutbound,conv)))));
        return F.Disp(All("r",R,All("alpha",R,Imp(Pos(r),Imp(new Formula.Relation(r,FormulaRelationOperator.LessThan,F.D(1)),
            Ex("A",Clm(R,hk,Clm(R,hf,hf)),And(raw,All("c",R,Imp(Pos(c),body)))))))));
    }
}
