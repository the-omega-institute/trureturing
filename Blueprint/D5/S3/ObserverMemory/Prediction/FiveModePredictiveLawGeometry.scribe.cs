using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModePredictiveLawGeometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite-horizon geometry and exact startup cutoffs of the actual five-mode source.",
        H("Five Mode Predictive Law Geometry"),
        Blocks(
            Paragraph(Text("The source has states Fin 5, visible symbols Fin 4, and B is visible code 2. "
                + "Its transition and observation are those of FiniteStartFiveModeSource. "
                + "Admissibility is p>0, q>0, r>0 and p+q+r<1. Put s=p+q, a=1-s, b=1-r and c=1-s-r. "
                + "These conditions include p=q and r=p+q. Every pure law is the actual source futureWordWeight from its point mass. "
                + "The empty law is initialWordWeight from the uniform initial vector and predicts Y0.")),
            Paragraph(Text("LawProfile is the dependent family of real word weights on Fin H to Visible, for every natural H. "
                + "ProbabilityProfile means nonnegative entries and total mass one at each H. CoherentProfile adds pointwise consistency "
                + "under deleting the final read. TV is the finite half-sum of absolute mass differences. "
                + "profileDistance is its supremum over finite horizons; H=0 contributes zero for probability profiles. "
                + "mixtureLaw x is x times pureLaw 2 plus 1-x times pureLaw 4. The finite TV identity also holds for real signed mixture coordinates; "
                + "probability and supremum claims below restrict them to [0,1].")),
            Paragraph(Text("FirstExit true selects a first non-B symbol 0; FirstExit false selects a first non-B symbol in {1,3}. "
                + "exitMass sums this event in a finite word. firstBExitMass F n z sums words of horizon n+1 beginning with B "
                + "whose remaining n symbols have FirstExit z. Thus at horizon H>=1 the displayed powers use n=H-1. "
                + "These are finite cylinders, with no conditioning on an infinite all-B history.")),
            Paragraph(Text("On unequal holding probabilities theta=min(a,b)/max(a,b). minority theta k is theta^k/(1+theta^k). "
                + "orientedMixture z is mixtureLaw (1-z) when a>b and mixtureLaw z otherwise. dominantLaw is pureLaw 2 when a>b and pureLaw 4 otherwise. "
                + "cutoff t e is the natural ceiling of log((1-e)/e)/abs(log t), using the natural logarithm; N2 is cutoff theta (2 epsilon). "
                + "actualStartupLaw k denotes the actual law after B^(k+1); actualStartupDistance k is its profileDistance from dominantLaw. The actual startup index k belongs to the acquired word B^(k+1). The equality r=p+q is treated by the half-mixture statements.")),
            Paragraph(Text("cappedClassLaw has mathematical labels State+Fin L: a pure label denotes its pure law and a startup label k denotes the actual law after B^(k+1). "
                + "fixedClassLaw has labels State+Unit and denotes the one startup law after B^L. OptionCase uses the empty law at None and the given class law at Some. "
                + "These label families classify the stated history domains. They do not provide a recording length to an autonomous update. "
                + "PostreadLawSet and InitializedLawSet are images of actual positive histories, excluding or including the empty history respectively.")),
            Entry("coherent_mixture_geometry", "One coherent family and both exact geometries",
                Admits(All("x", Real, All("z", Real, ImpliesF(AndF(UnitInterval(X), UnitInterval(Z)),
                    AndF(Coherent(Mix(X)), AndF(All("H", Nat, EqF(Tv(Mix(X),Mix(Z),Horizon), Mul(Abs(Sub(X,Z)),Factor(Horizon)))),
                        EqF(Distance(Mix(X),Mix(Z)),Abs(Sub(X,Z))))))))),
                "The finite laws are normalized, nonnegative and consistent under deletion of the last read."),
            Entry("branch_exit_masses", "Finite first-exit probabilities",
                Admits(All("H", Nat, AndF(EqF(Exit(Pure(D(2)),Horizon,TrueValue),D(0)),
                    AndF(EqF(Exit(Pure(D(4)),Horizon,TrueValue),Sub(D(1),Pow(Bhold,Horizon))),
                        AndF(EqF(Exit(Pure(D(2)),Horizon,FalseValue),Sub(D(1),Pow(A,Horizon))),
                            EqF(Exit(Pure(D(4)),Horizon,FalseValue),D(0))))))),
                "The selected first exit is measured within each finite word, before any later source motion."),
            Entry("empty_first_B_exit_masses", "The two empty-law cylinder masses",
                Admits(All("H", Nat, AndF(EqF(FirstBExit(Empty,Horizon,TrueValue),Div(Sub(D(1),Pow(Bhold,Horizon)),D(5))),
                    EqF(FirstBExit(Empty,Horizon,FalseValue),Div(Sub(D(1),Pow(A,Horizon)),D(5)))))),
                "At horizon H+1 the masses are (1-b^H)/5 and (1-a^H)/5. Equivalently their exponent is H-1 at positive total horizon H."),
            Entry("pure_first_B_exit_zero", "A pure start forbids one exit category",
                Admits(All("i", State, OrF(All("H",Nat,EqF(FirstBExit(Pure(I),Horizon,TrueValue),D(0))),
                    All("H",Nat,EqF(FirstBExit(Pure(I),Horizon,FalseValue),D(0)))))),
                "A first B from a pure mode enters only one of the two hidden B branches."),
            Entry("empty_pure_separation", "Empty versus every pure law",
                Admits(All("i",State,Le(Div(D(1),D(5)),Distance(Empty,Pure(I))))),
                "One impossible pure first-B exit category has empty-law mass tending to one fifth along finite horizons."),
            Entry("pure_pair_separation", "All distinct pure laws are separated",
                Admits(All("i",State,All("j",State,ImpliesF(Ne(I,J),Le(Kappa,Distance(Pure(I),Pure(J))))))),
                "The 2-versus-4 pair has complete distance one; every other pair has a positive singleton-coordinate gap."),
            Entry("oriented_geometry", "Geometry in both orientations",
                Admits(All("z",Real,All("w",Real,ImpliesF(AndF(UnitInterval(Z),UnitInterval(W)),
                    AndF(Coherent(Oriented(Z)),AndF(All("H",Nat,EqF(Tv(Oriented(Z),Oriented(W),Horizon),Mul(Abs(Sub(Z,W)),Factor(Horizon)))),
                        EqF(Distance(Oriented(Z),Oriented(W)),Abs(Sub(Z,W))))))))),
                "Reversing which branch is dominant changes the mixture coordinate and preserves both metric formulas."),
            Entry("actual_startup_geometry", "Actual startup distances", StartupGeometryFormula(),
                "Every acquired startup has one coherent law, exact pair distance, and exact distance delta_k from the dominant law."),
            Entry("equality_startup_geometry", "The separate half-mixture stratum", EqualityStartupFormula(),
                "When r=p+q all finite startup lengths give the half-mixture, whose distances from pure 2 and pure 4 are one half."),
            Entry("startup_coordinate_injective", "Unequal startup coordinates are injective",
                Unequal(Call("Injective",Call("startupCoordinate",P,Q,R))),
                "The strict minority sequence distinguishes all finite startup indices in either orientation."),
            Entry("interior_mixture_distinct", "An interior mixture is a separate law",
                Admits(All("x",Real,ImpliesF(AndF(Pos(X),Less(X,D(1))),
                    AndF(All("i",State,Ne(Mix(X),Pure(I))),Ne(Mix(X),Empty))))),
                "Both branch coordinates remain positive, so no interior mixture is a pure or empty law."),
            Entry("actual_startup_injective", "Distinct actual startup lengths",
                Unequal(Call("Injective",Call("actualStartupLaw",P,Q,R))),
                "actualStartupLaw k is actualFutureWordWeight after the acquired word B^(k+1)."),
            Entry("actual_predictive_class_distinctness", "Actual predictive-law class distinctness", DistinctnessFormula(),
                "All five pure laws differ; the empty law is additional; every finite startup law is interior and differs from them."),
            Entry("actual_cutoff_geometry", "Cutoff and decay in the actual metric", ActualCutoffFormula(),
                "N2 is the first non-strict actual distance threshold. The formula, earlier strict inequalities, exact ties and decay are simultaneous."),
            Entry("startup_midpoint_tail_bound", "One coherent midpoint bounds the tail", MidpointFormula(),
                "The midpoint beta=delta_N2/2 is within epsilon of the dominant law and every actual startup law with k>=N2."),
            Entry("capped_predictive_classes", "Classes under a length cap", CappedFormula(),
                "For L>=2 and a!=b there are L+5 realized post-read law classes, with both realization and exhaustive coverage."),
            Entry("fixed_length_predictive_classes", "Classes at one fixed length", FixedFormula(),
                "For every admissible triple and L>=2 the single fixed-length history domain has six realized law classes."),
            Entry("initialized_capped_class_count", "The capped empty boundary adds one class",
                Unequal(All("L",Nat,ImpliesF(Le(D(2),Length),AndF(Call("Injective",OptionCase(Capped(Length))),
                    EqF(Card(Call("Option",CappedLabels(Length))),Add(Length,D(6))))))),
                "The initialized capped family has L+6 distinct laws. This count includes the queryable empty boundary."),
            Entry("equality_predictive_classes", "Equality has six or seven law classes", EqualityClassesFormula(),
                "The all-length equality domain has six post-read laws and an additional initialized empty law, with actual realization and coverage."),
            Entry("startup_transient_separation", "Every pre-cutoff startup class is separate", TransientFormula(),
                "Every index strictly below N2 is more than 2 epsilon from each pure law and from the empty law."),
            Entry("unequal_exact_classes_countably_infinite", "Countably infinite exact images",
                Unequal(AndF(Call("CountableSet",PostreadSet),AndF(Call("Infinite",PostreadSet),
                    AndF(Call("CountableSet",InitializedSet),Call("Infinite",InitializedSet))))),
                "All finite actual histories form a countable domain, while the positive all-B startup orbit supplies an injection from the naturals."),
            Entry("five_mode_predictive_geometry", "Actual five-mode predictive geometry",
                Admits(Call("PredictiveGeometry",P,Q,R)),
                "PredictiveGeometry collects the exact branch support and holding masses, finite and complete mixture geometry, coherence, positive kappa, "
                    + "pure, singleton, mixture and empty separations, finite empty exit masses, actual startup laws, exact cutoff, the coherent midpoint tail bound, "
                    + "fixed and capped class injections, equality classes and the unequal countably infinite images. Its only premise is source admissibility."))));

    private static DocumentBlock.Describe Entry(string name,string title,Formula formula,string text) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModePredictiveLawGeometry."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))),DescribeRole.Theorem);
    private static Formula Call(string name,params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula All(string name,Formula type,Formula body) => Seq(Open,Forall,Sp,F.Id(name),Colon,Sp,type,Comma,Esc,body,Close);
    private static Formula Some(string name,Formula type,Formula body) => Seq(Open,Exists,Sp,F.Id(name),Colon,Sp,type,Comma,Esc,body,Close);
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
    private static Formula Word(Formula h) => Seq(Call("Fin",h),To,Sp,F.Id("Visible"));
    private static Formula Pure(Formula i) => Call("pureLaw",P,Q,R,i);
    private static Formula Mix(Formula x) => Call("mixtureLaw",P,Q,R,x);
    private static Formula Oriented(Formula x) => Call("orientedMixture",P,Q,R,x);
    private static Formula Value(Formula law,Formula h,Formula w) => Call("word",law,h,w);
    private static Formula Tv(Formula f,Formula g,Formula h) => Call("TV",Call("at",f,h),Call("at",g,h));
    private static Formula Distance(Formula f,Formula g) => Call("profileDistance",f,g);
    private static Formula Coherent(Formula f) => Call("CoherentProfile",f);
    private static Formula Exit(Formula f,Formula h,Formula b) => Call("exitMass",f,h,b);
    private static Formula FirstBExit(Formula f,Formula h,Formula b) => Call("firstBExitMass",f,h,b);
    private static Formula Factor(Formula h) => Sub(D(1),Pow(Call("min",A,Bhold),h));
    private static Formula Delta(Formula k) => Call("minority",Theta,k);
    private static Formula Startup(Formula k) => Call("replicate",Add(k,D(1)),F.Id("B"));
    private static Formula Actual(Formula h) => Call("actualFutureWordWeight",P,Q,R,h);
    private static Formula TendsToZero(Formula f) => Call("Tendsto",f,F.Id("atTop"),Call("nhds",D(0)));
    private static Formula Critical(Formula t,Formula e) => Div(Call("log",Div(Sub(D(1),e),e)),Abs(Call("log",t)));
    private static Formula StartupGeometryFormula() => Unequal(All("k",Nat,All("l",Nat,AndF(Coherent(Actual(Startup(K))),
        AndF(EqF(Distance(Actual(Startup(K)),Actual(Startup(F.Id("l")))),Abs(Sub(Delta(K),Delta(F.Id("l"))))),
            EqF(Distance(Actual(Startup(K)),Dominant),Delta(K)))))));
    private static Formula EqualityStartupFormula() => Admits(ImpliesF(EqF(R,Add(P,Q)),All("k",Nat,
        AndF(All("H",Nat,All("w",Word(Horizon),EqF(Value(Actual(Startup(K)),Horizon,W),Value(Mix(Div(D(1),D(2))),Horizon,W)))),
            AndF(Coherent(Empty),AndF(EqF(Distance(Mix(Div(D(1),D(2))),Pure(D(2))),Div(D(1),D(2))),
                EqF(Distance(Mix(Div(D(1),D(2))),Pure(D(4))),Div(D(1),D(2)))))))));
    private static Formula DistinctnessFormula() => Admits(AndF(Call("Injective",Call("pureLaw",P,Q,R)),
        AndF(All("i",State,Ne(Empty,Pure(I))),All("k",Nat,AndF(All("i",State,Ne(Actual(Startup(K)),Pure(I))),Ne(Actual(Startup(K)),Empty))))));
    private static Formula ActualCutoffFormula() => SmallError(AndF(Pos(Ntwo),AndF(EqF(Ntwo,Call("ceilNat",Critical(Theta,Mul(D(2),Epsilon)))),
        AndF(All("k",Nat,IffF(Le(Distance(Actual(Startup(K)),Dominant),Mul(D(2),Epsilon)),Le(Ntwo,K))),
            AndF(All("i",Nat,ImpliesF(Less(I,Ntwo),Less(Mul(D(2),Epsilon),Distance(Actual(Startup(I)),Dominant)))),
                AndF(IffF(EqF(Distance(Actual(Startup(Ntwo)),Dominant),Mul(D(2),Epsilon)),EqF(Critical(Theta,Mul(D(2),Epsilon)),Call("castReal",Ntwo))),
                    TendsToZero(Call("actualStartupDistance",P,Q,R))))))));
    private static Formula MidpointFormula() => SmallError(AndF(Coherent(Oriented(Beta)),AndF(Le(Distance(Dominant,Oriented(Beta)),Epsilon),
        All("k",Nat,ImpliesF(Le(Ntwo,K),Le(Distance(Actual(Startup(K)),Oriented(Beta)),Epsilon))))));
    private static Formula Capped(Formula l) => Call("cappedClassLaw",P,Q,R,l);
    private static Formula Fixed(Formula l) => Call("fixedClassLaw",P,Q,R,l);
    private static Formula CappedLabels(Formula l) => Call("Sum",State,Call("Fin",l));
    private static Formula FixedLabels => Call("Sum",State,F.Id("Unit"));
    private static Formula OptionCase(Formula law) => Call("OptionCase",Empty,law);
    private static Formula Card(Formula type) => Call("card",type);
    private static Formula History => Call("List",F.Id("Visible"));
    private static Formula Hvalue => F.Id("h");
    private static Formula Mass => Call("historyMass",P,Q,R,Hvalue);
    private static Formula Hnonempty => Ne(Hvalue,Call("nil"));
    private static Formula Hlength => Call("length",Hvalue);
    private static Formula ClassAt(Formula law,Formula t) => Call("apply",law,t);
    private static Formula Realize(Formula law,Formula labels,Formula domain) => All("t",labels,Some("h",History,
        AndF(domain,AndF(Pos(Mass),EqF(Actual(Hvalue),ClassAt(law,T))))));
    private static Formula Cover(Formula law,Formula labels,Formula domain) => All("h",History,ImpliesF(AndF(domain,Pos(Mass)),
        Some("t",labels,EqF(Actual(Hvalue),ClassAt(law,T)))));
    private static Formula CappedFormula() => Unequal(All("L",Nat,ImpliesF(Le(D(2),Length),AndF(Call("Injective",Capped(Length)),
        AndF(Realize(Capped(Length),CappedLabels(Length),AndF(Hnonempty,Le(Hlength,Length))),
            AndF(Cover(Capped(Length),CappedLabels(Length),AndF(Hnonempty,Le(Hlength,Length))),EqF(Card(CappedLabels(Length)),Add(Length,D(5)))))))));
    private static Formula FixedFormula() => Admits(All("L",Nat,ImpliesF(Le(D(2),Length),AndF(Call("Injective",Fixed(Length)),
        AndF(Realize(Fixed(Length),FixedLabels,EqF(Hlength,Length)),AndF(Cover(Fixed(Length),FixedLabels,EqF(Hlength,Length)),EqF(Card(FixedLabels),D(6))))))));
    private static Formula EqualityClassesFormula() => Admits(ImpliesF(EqF(R,Add(P,Q)),AndF(Call("Injective",Fixed(D(2))),
        AndF(Realize(Fixed(D(2)),FixedLabels,Hnonempty),AndF(Cover(Fixed(D(2)),FixedLabels,Hnonempty),
            AndF(Call("Injective",OptionCase(Fixed(D(2)))),AndF(EqF(Card(FixedLabels),D(6)),EqF(Card(Call("Option",FixedLabels)),D(7)))))))));
    private static Formula TransientFormula() => SmallError(All("k",Nat,ImpliesF(Less(K,Ntwo),AndF(All("j",State,
        Less(Mul(D(2),Epsilon),Distance(Actual(Startup(K)),Pure(J)))),Less(Mul(D(2),Epsilon),Distance(Actual(Startup(K)),Empty))))));
    private static Formula Real => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula State => F.Id("State");
    private static Formula P => F.Id("p"); private static Formula Q => F.Id("q"); private static Formula R => F.Id("r");
    private static Formula X => F.Id("x"); private static Formula Z => F.Id("z"); private static Formula W => F.Id("w");
    private static Formula I => F.Id("i"); private static Formula J => F.Id("j"); private static Formula K => F.Id("k");
    private static Formula T => F.Id("t"); private static Formula Epsilon => F.Id("epsilon");
    private static Formula Horizon => F.Id("H"); private static Formula Length => F.Id("L");
    private static Formula A => Call("a",P,Q); private static Formula Bhold => Call("b",R);
    private static Formula Theta => Call("theta",P,Q,R); private static Formula Kappa => Call("kappa",P,Q,R);
    private static Formula Ntwo => Call("N2",P,Q,R,Epsilon);
    private static Formula Beta => Div(Delta(Ntwo),D(2));
    private static Formula Empty => Call("emptyLaw",P,Q,R); private static Formula Dominant => Call("dominantLaw",P,Q,R);
    private static Formula TrueValue => F.Id("true"); private static Formula FalseValue => F.Id("false");
    private static Formula PostreadSet => Call("postreadLawSet",P,Q,R); private static Formula InitializedSet => Call("initializedLawSet",P,Q,R);
}
