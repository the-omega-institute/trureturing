using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction.FiveModePredictiveLawGeometry;

internal sealed class FiveModePredictiveLawGeometryCoreDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-horizon mixture geometry and exact startup cutoffs of the actual five-mode source.",
        H("Five Mode Predictive Law Geometry Core"),
        Blocks(
            Paragraph(Text("The literal five-state source has visible symbols Fin 4, with B as code 2. Admissibility is p>0, q>0, r>0 and p+q+r<1. "
                + "Write a=1-p-q, b=1-r and c=1-p-q-r. Pure and empty laws are the actual future and initial word laws of FiniteStartFiveModeSource. "
                + "LawProfile contains every finite horizon. ProbabilityProfile requires nonnegative weights of total mass one; CoherentProfile also requires consistency under deleting the final read.")),
            Paragraph(Text("Finite total variation is half the sum of absolute mass differences; profileDistance is its supremum over finite horizons. "
                + "mixtureLaw x combines pure laws 2 and 4 with weights x and 1-x. Finite TV holds for real signed coordinates; probability and supremum statements restrict coordinates to [0,1].")),
            Paragraph(Text("For unequal a and b, theta=min(a,b)/max(a,b), minority theta k=theta^k/(1+theta^k), and orientedMixture z puts weight z on the minority branch. "
                + "The acquired startup word is B^(k+1). cutoff t e is the natural ceiling of log((1-e)/e)/abs(log t), and N2=cutoff theta (2 epsilon). "
                + "The first accepted index uses a non-strict inequality, including exact ties.")),
            Entry("branch_all_B", "Literal all-B holding masses",
                Parameters(All("H", Nat, AndF(EqF(Value(Pure(D(2)), Horizon, ConstantB), Pow(A, Horizon)),
                    EqF(Value(Pure(D(4)), Horizon, ConstantB), Pow(Bhold, Horizon))))),
                "Both masses are powers at every finite horizon, including H=0."),
            Entry("branch_word_overlap", "Exact common branch support",
                Admits(All("H", Nat, All("w", Word(Horizon), IffF(AndF(Pos(Value(Pure(D(2)), Horizon, W)),
                    Pos(Value(Pure(D(4)), Horizon, W))), EqF(W, ConstantB))))),
                "The first exit categories are disjoint, so the common positive support is exactly the all-B word."),
            Entry("branch_finite_tv", "Finite branch total variation",
                Admits(All("H", Nat, EqF(Tv(Pure(D(2)), Pure(D(4)), Horizon), Factor(Horizon)))),
                "The finite value is 1-min(a,b)^H. Its horizon dependence is retained."),
            Entry("mixture_finite_tv", "Finite mixture total variation",
                Admits(All("x", Real, All("z", Real, All("H", Nat,
                    EqF(Tv(Mix(X), Mix(Z), Horizon), Mul(Abs(Sub(X,Z)), Factor(Horizon))))))),
                "Homogeneity of the signed difference combines with the actual branch overlap."),
            Entry("mixture_profile_distance", "The all-horizon mixture metric",
                Admits(All("x", Real, All("z", Real, ImpliesF(AndF(UnitInterval(X), UnitInterval(Z)),
                    EqF(Distance(Mix(X), Mix(Z)), Abs(Sub(X,Z))))))),
                "Finite holding powers tend to zero, so the supremum equals the coordinate distance."),
            Entry("kappa_positive", "Positive uniform separation constant", Admits(Pos(Kappa)),
                "kappa is min(c,p,q,a,c*s/(s+r),a*p/s,a*q/s,1/25), with every term strictly positive."),
            Entry("singleton_mixture_separation", "Singleton versus any mixture",
                Admits(All("x",Real,ImpliesF(UnitInterval(X),All("j",State,ImpliesF(Singleton(J),
                    Le(Kappa,Distance(Pure(J),Mix(X)))))))),
                "The coordinate and finite-event estimates apply without generic-parameter exclusions."),
            Entry("empty_mixture_separation", "Empty versus any mixture",
                Admits(All("x",Real,ImpliesF(UnitInterval(X),Le(Div(D(1),D(2,5)),Distance(Empty,Mix(X)))))),
                "The two one-step event gaps give the universal lower bound one twenty-fifth."),
            Entry("minority_strictAnti", "Strict geometric monotonicity",
                All("t",Real,ImpliesF(AndF(Pos(T),Less(T,D(1))),Call("StrictAnti",Call("minority",T)))),
                "The finite startup minority coordinate decreases at every step when 0<t<1."),
            Entry("minority_tendsto_zero", "Geometric decay",
                All("t",Real,ImpliesF(AndF(Pos(T),Less(T,D(1))),TendsToZero(Call("minority",T)))),
                "The limit concerns finite startup coordinates, not an observed infinite history."),
            Entry("cutoff_first_nonstrict", "Exact first non-strict cutoff and ties", CutoffFormula(),
                "The literal natural ceiling is positive, accepts equality at the threshold, and excludes all earlier indices."),
            Entry("actual_oriented_startup", "The actual acquired startup law",
                Unequal(All("k",Nat,All("H",Nat,All("w",Word(Horizon),
                    EqF(Value(Actual(Startup(K)),Horizon,W),Value(Oriented(Delta(K)),Horizon,W)))))),
                "The acquired all-B posterior from the literal source gives G_delta at every future word."),
            Entry("actual_startup_cutoff", "The source-specific minority cutoff",
                SmallError(CutoffProperties(Theta,Mul(D(2),Epsilon),Ntwo)),
                "Both unequal orientations have the same exact minority threshold index N2."))));

    private static DocumentBlock.Describe Entry(string name,string title,Formula formula,string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry/Core."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula Call(string name,params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula All(string name,Formula type,Formula body) => Seq(Open,Forall,Sp,F.Id(name),Colon,Sp,type,Comma,Esc,body,Close);
    private static Formula Parameters(Formula body) => All("p",Real,All("q",Real,All("r",Real,body)));
    private static Formula Admits(Formula body) => Parameters(ImpliesF(Call("admissible",P,Q,R),body));
    private static Formula Unequal(Formula body) => Admits(ImpliesF(Ne(A,Bhold),body));
    private static Formula SmallError(Formula body) => Unequal(All("epsilon",Real,ImpliesF(AndF(Pos(Mul(D(2),Epsilon)),Less(Mul(D(2),Epsilon),Kappa)),body)));
    private static Formula EqF(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Ne(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Less(Formula a,Formula b) => Seq(a,Sp,Lt,Sp,b);
    private static Formula Pos(Formula a) => Less(D(0),a);
    private static Formula AndF(Formula a,Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula OrF(Formula a,Formula b) => Seq(Open,a,Sp,Lor,Sp,b,Close);
    private static Formula ImpliesF(Formula a,Formula b) => Seq(Open,a,Sp,Rightarrow,Sp,b,Close);
    private static Formula IffF(Formula a,Formula b) => Seq(Open,a,Sp,Iff,Sp,b,Close);
    private static Formula Add(Formula a,Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Sub(Formula a,Formula b) => Seq(Open,a,Minus,b,Close);
    private static Formula Mul(Formula a,Formula b) => Seq(Open,a,Star,b,Close);
    private static Formula Div(Formula a,Formula b) => new Formula.Fraction(a,b);
    private static Formula Pow(Formula a,Formula b) => Seq(Open,a,Close,Caret,Grp(b));
    private static Formula Abs(Formula a) => Call("abs",a);
    private static Formula UnitInterval(Formula x) => Seq(x,Sp,InMacro,Sp,Call("Icc",D(0),D(1)));
    private static Formula Singleton(Formula i) => OrF(EqF(i,D(0)),OrF(EqF(i,D(1)),EqF(i,D(3))));
    private static Formula Word(Formula h) => Seq(Call("Fin",h),To,Sp,F.Id("Visible"));
    private static Formula Pure(Formula i) => Call("pureLaw",P,Q,R,i);
    private static Formula Mix(Formula x) => Call("mixtureLaw",P,Q,R,x);
    private static Formula Oriented(Formula x) => Call("orientedMixture",P,Q,R,x);
    private static Formula Value(Formula law,Formula h,Formula w) => Call("word",law,h,w);
    private static Formula Tv(Formula f,Formula g,Formula h) => Call("TV",Call("at",f,h),Call("at",g,h));
    private static Formula Distance(Formula f,Formula g) => Call("profileDistance",f,g);
    private static Formula Factor(Formula h) => Sub(D(1),Pow(Call("min",A,Bhold),h));
    private static Formula Delta(Formula k) => Call("minority",Theta,k);
    private static Formula Startup(Formula k) => Call("replicate",Add(k,D(1)),F.Id("B"));
    private static Formula Actual(Formula h) => Call("actualFutureWordWeight",P,Q,R,h);
    private static Formula TendsToZero(Formula f) => Call("Tendsto",f,F.Id("atTop"),Call("nhds",D(0)));
    private static Formula Critical(Formula t,Formula e) => Div(Call("log",Div(Sub(D(1),e),e)),Abs(Call("log",t)));
    private static Formula CutoffProperties(Formula t,Formula e,Formula n) => AndF(Pos(n),AndF(Le(Call("minority",t,n),e),
        AndF(All("i",Nat,ImpliesF(Less(I,n),Less(e,Call("minority",t,I)))),AndF(All("k",Nat,IffF(Le(Call("minority",t,K),e),Le(n,K))),
            IffF(EqF(Call("minority",t,n),e),EqF(Critical(t,e),Call("castReal",n)))))));
    private static Formula CutoffFormula() => All("t",Real,All("e",Real,ImpliesF(AndF(AndF(Pos(T),Less(T,D(1))),
        AndF(Pos(F.Id("e")),Less(F.Id("e"),Div(D(1),D(2))))),CutoffProperties(T,F.Id("e"),Call("cutoff",T,F.Id("e"))))));
    private static Formula Real => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula State => F.Id("State");
    private static Formula P => F.Id("p"); private static Formula Q => F.Id("q"); private static Formula R => F.Id("r");
    private static Formula X => F.Id("x"); private static Formula Z => F.Id("z"); private static Formula W => F.Id("w");
    private static Formula I => F.Id("i"); private static Formula J => F.Id("j"); private static Formula K => F.Id("k");
    private static Formula T => F.Id("t"); private static Formula Epsilon => F.Id("epsilon");
    private static Formula Horizon => F.Id("H");     private static Formula A => Call("a",P,Q); private static Formula Bhold => Call("b",R);
    private static Formula Theta => Call("theta",P,Q,R); private static Formula Kappa => Call("kappa",P,Q,R);
    private static Formula Ntwo => Call("N2",P,Q,R,Epsilon);
    private static Formula Empty => Call("emptyLaw",P,Q,R);     private static Formula ConstantB => Call("constant",F.Id("B"));
}
