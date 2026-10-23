using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModeStrictStartupDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict startup nonrecurrence strengthens the initialized lower bound for the unrestricted five-mode generated observer.",
        H("Five Mode Strict Startup and Initialized Count"), Blocks(
            Paragraph(Text("Use the unchanged passive five-mode source with positive p,q,r and p+q+r<1. Its holding probabilities are a=1-p-q and b=1-r, with a different from b. The visible alphabet is Fin 4 in Lean order 0,1,B,3, B=2. The minority coordinate at startup index k is delta(k)=theta^k/(1+theta^k), theta=min(a,b)/max(a,b). Every finite startup history B^(k+1) has positive actual probability. startup(O,k) is the configuration obtained by the actual fold of the one total update on that history.")),
            Paragraph(Text("A GeneratedObserver on Z has initialization, a total deterministic update, and normalized nonnegative emission rows everywhere. Its decoded law is generatedLaw using those same rows and that same update at every hypothetical symbol. Zero forecast probabilities do not remove actual legal updates. All configurations of the finite carrier count, including initialization and configurations used only by generated words. A hidden source mode is a proof coordinate, without supplying an extra observer input.")),
            Paragraph(Text("Accurate(O,p,q,r,epsilon,true) quantifies every positive finite actual history including the empty history and every natural future horizon. At the empty history the source future begins with Y0; after a nonempty acquired history it begins with the next source step. Guarantee below is the original equivalent formulation restricted to positive horizons; the original guarantee_accurate supplier extends it to horizon zero by normalization. No positive actual history, however rare, is discarded.")),
            Entry("startup_collision_strict",DescribeRole.Theorem,ObserverParameters(SourceParameters(All("epsilon",Real,
                All("i",Nat,All("j",Nat,Implies(And(Admissible,Unequal,Accurate,Lt(I,JJ),Equal(Startup(I),Startup(JJ))),
                    Lt(Delta(I),TwiceEpsilon))))))),
                "A collision gives a positive B period. The existing nonstrict collision theorem bounds delta(i) by 2*epsilon. At equality the recurring decoder is within epsilon of both the dominant pure law and the startup law at index i. FiveModePeriodicDiameter.periodic_diameter_obstruction excludes that equality. This strict theorem itself requires no small-error hypothesis beyond its complete accuracy assumption."),
            Entry("J",DescribeRole.Definition,SourceParameters(All("epsilon",Real,Equal(CutoffJ,
                Call("ifThenElse",Equal(Delta(CutoffN2),TwiceEpsilon),Add(CutoffN2,One),CutoffN2)))),
                "N2 is the first nonstrict delta(k)<=2*epsilon cutoff. In the unequal small-error domain, J is the first strict delta(k)<2*epsilon cutoff: J>0, delta(J)<2*epsilon, and every i<J has delta(i)>=2*epsilon. Hence J=N2 away from equality and J=N2+1 at equality, with N2<=J<=N1."),
            Entry("startup_never_recurs_before_J",DescribeRole.Theorem,ObserverParameters(SourceParameters(All("epsilon",Real,
                All("i",Nat,All("j",Nat,Implies(And(SmallDomain,Accurate,Lt(I,CutoffJ),Lt(I,JJ)),
                    F.NotEqual(Startup(I),Startup(JJ)))))))),
                "The later index j is unrestricted above. This is stronger than pairwise distinctness of a finite initial segment."),
            Entry("generated_initialized_lower",DescribeRole.Theorem,FiniteObserverParameters(SourceParameters(All("epsilon",Real,
                Implies(And(SmallDomain,Guarantee),Le(Lower,Call("card",Z)))))),
                "The lower bound uses the entire finite carrier. Select the five actually reached, exact pure-law configurations supplied by recurrent_pair_rigidity. For each k<N1, the startup profile is more than epsilon from every one of those exact pure laws: the dominant distance is delta(k), the other ambiguous distance is 1-delta(k)>=1/2, and singleton separation is at least kappa. The original postread_initialization_extra_state supplier separates initialization from each reached selection and startup configuration."),
            Paragraph(Text("Put M=min(N1,J+1). The exact pure selections and the first M startup configurations give a disjoint injection from State plus Fin M into Z. If two startup indices in that segment differ, the smaller is strictly below J, so the strict nonrecurrence theorem separates them, including the possible additional index J. Adding initialization gives an injection from Option(State plus Fin M), whose cardinality is 6+M. No assertion removes generated-only configurations or assumes a unique synchronized recurrent presentation.")),
            Entry("initialized_generated_strict_minimum",DescribeRole.Theorem,SourceParameters(All("epsilon",Real,
                Implies(SmallDomain,And(
                    All("n",Nat,Implies(Call("Attainable",P,Q,R,Epsilon,N),Le(Lower,N))),
                    Le(Lower,Minimum),Le(Minimum,Add(Six,CutoffN1)),
                    Implies(Lt(CutoffN2,CutoffN1),Le(Add(Seven,CutoffN2),Minimum)),
                    Implies(Equal(Delta(CutoffN2),TwiceEpsilon),Implies(Le(Add(CutoffN2,Two),CutoffN1),
                        Le(Add(Eight,CutoffN2),Minimum))))))),
                "Attainable is the existing existence predicate for accurate GeneratedObserver(Fin n), and Minimum denotes its existing attained minimum with the displayed admissibility and error hypotheses. Applying the carrier lower bound to every attainable n and to minimum_attained yields these conclusions. The existing source-exact truncation construction still gives the upper bound 6+N1. The result supplies a lower bound, not a complete unrestricted minimization theorem."))));

    private static Formula Guarantee => All("h",History,Implies(Lt(Zero,Call("historyMass",P,Q,R,Hist)),
        All("H",Nat,Implies(Lt(Zero,HH),Le(Call("totalVariation",
            Call("actualFutureWordWeight",P,Q,R,Hist,HH),
            Call("generatedLaw",Call("update",O),Call("row",O),Call("run",Call("toObserver",O),Hist),HH)),Epsilon)))));
    private static Formula Accurate => Call("Accurate",Call("toObserver",O),P,Q,R,Epsilon,Call("true"));
    private static Formula SmallDomain => And(Admissible,Unequal,Lt(Zero,TwiceEpsilon),Lt(TwiceEpsilon,Call("kappa",P,Q,R)));
    private static Formula Admissible => Call("admissible",P,Q,R);
    private static Formula Unequal => F.NotEqual(Call("a",P,Q),Call("b",R));
    private static Formula Lower => Add(Six,Call("min",CutoffN1,Add(CutoffJ,One)));
    private static Formula Minimum => Call("minimum",Call("admissibilityProof",P,Q,R),Call("unequalProof",P,Q,R),
        Call("positiveErrorProof",Epsilon),Call("smallErrorProof",P,Q,R,Epsilon));
    private static Formula CutoffJ => Call("J",P,Q,R,Epsilon);
    private static Formula CutoffN1 => Call("N1",P,Q,R,Epsilon);
    private static Formula CutoffN2 => Call("N2",P,Q,R,Epsilon);
    private static Formula TwiceEpsilon => F.Multiply(Two,Epsilon);
    private static Formula Delta(Formula n) => Call("minority",Call("theta",P,Q,R),n);
    private static Formula Startup(Formula n) => Call("startupState",Call("toObserver",O),n);
    private static DocumentBlock.Describe Entry(string name,DescribeRole role,Formula statement,string note) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModeStrictStartup."+name),
            H(name.Replace('_',' ')),StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(note))),role);
    private static Formula ObserverParameters(Formula b) => All("Z",Call("Type"),All("O",Call("GeneratedObserver",Z),b));
    private static Formula FiniteObserverParameters(Formula b) => All("Z",Call("Type"),Seq(OpenBracket,Call("Fintype",Z),CloseBracket,Sp,
        All("O",Call("GeneratedObserver",Z),b)));
    private static Formula SourceParameters(Formula b) => All("p",Real,All("q",Real,All("r",Real,b)));
    private static Formula All(string n,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Call(string n,params Formula[] a) => F.Call(n,a);
    private static Formula Equal(Formula l,Formula r) => F.Equal(l,r);
    private static Formula Le(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThanOrEqual,r);
    private static Formula Lt(Formula l,Formula r) => new Formula.Relation(l,FormulaRelationOperator.LessThan,r);
    private static Formula Implies(Formula l,Formula r) => new Formula.Logic(l,FormulaLogicOperator.Implies,r);
    private static Formula And(params Formula[] xs) => xs.Aggregate((l,r)=>new Formula.Logic(l,FormulaLogicOperator.And,r));
    private static Formula Add(Formula l,Formula r) => F.Add(l,r);
    private static Formula Z => F.Id("Z");
    private static Formula O => F.Id("O");
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula Epsilon => F.Id("epsilon");
    private static Formula I => F.Id("i");
    private static Formula JJ => F.Id("j");
    private static Formula N => F.Id("n");
    private static Formula Hist => F.Id("h");
    private static Formula HH => F.Id("H");
    private static Formula History => Call("List",Call("Visible"));
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula Zero => D(0);
    private static Formula One => D(1);
    private static Formula Two => D(2);
    private static Formula Six => D(6);
    private static Formula Seven => D(7);
    private static Formula Eight => D(8);
}
