using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModeAutonomousSharpCountDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sharp finite autonomous common-law observers for the actual finite-start source.",
        H("Five Mode Autonomous Sharp Count"),
        Blocks(
            Paragraph(Text("The source is the literal FiniteStartFiveModeSource: State=Fin 5, Visible=Fin 4 and B=2, with uniform stationary initial distribution, p,q,r>0 and p+q+r<1. Set s=p+q, a=1-s, b=1-r and c=1-s-r. The separation constant is kappa=min(c,p,q,a,c*s/(s+r),a*p/s,a*q/s,1/25)>0. The parameter domain includes p=q and r=p+q. The empty law predicts Y0. After a nonempty actual history h, actualFutureWordWeight is the source conditional future law beginning immediately after the acquired word. An actual history has strictly positive historyMass.")),
            Paragraph(Text("Observer Z consists of an initial configuration, one total deterministic update Z times Visible to Z, and one fixed decoder Z to LawProfile. Its run is a left fold using only the retained configuration and the next acquired read. CoherentObserver means every fixed decoder is nonnegative, normalized at every natural horizon, and consistent under deleting the final symbol. This common-law contract imposes no self-generated symbol-product law and no equality between decoder conditioning and the decoder at an updated state. No hidden state, prehistory, recording length, clock or external age is an input.")),
            Paragraph(Text("Accuracy holds jointly for every actual positive finite history and every finite future horizon. The queryEmpty=true convention includes empty history; false permits queries only after reads. H=0 has the unique normalized empty word and contributes TV zero. Reached is the image of actual positive nonempty histories. FintypeCard counts the carrier, and NatCard of Reached counts its subtype. notNoneSet denotes {z | z is not None} in the displayed Option carrier, and univ denotes its entire displayed carrier. The universal bounds range over every type, every finite-carrier instance, every initial configuration, every total deterministic update and every common coherent decoder.")),
            Paragraph(Text("SharpState N is Option(State+Fin N): None is I, Some(Inl i) is Ri, and Some(Inr k) is Ak. encodeSource maps start to I, pure i to Ri, and startup k to Ak when k<N, or Rd otherwise. representative reads only the retained label. sharpUpdate is encodeSource after sourceUpdate of that representative, and is total on impossible actual extensions. Every singleton 0,1,3 resets every label to its matching pure label. On B, pure labels 0/4 go to 4 and 1/2/3 go to 2; Ak advances until it saturates at Rd. I goes to A0 when N>0, with Rd as its total fallback when N=0. foldSharp d N h denotes the fold of this update from None.")),
            Paragraph(Text("The dominant state d is 2 when a>b and 4 otherwise. On unequal holdings theta=min(a,b)/max(a,b) is in (0,1), delta_k=theta^k/(1+theta^k), and N2 is the finite positive first non-strict cutoff delta_N2<=2 epsilon. Its exact expression is ceilNat(log((1-2 epsilon)/(2 epsilon))/abs(log theta)). Every i<N2 is strict and a tie delta_N2=2 epsilon is allowed. Startup k denotes the actual acquired word B^(k+1); startupState O k is its actual observer run. The Bstep of an update is the map z to update z B, and iterate uses a finite natural exponent.")),
            Paragraph(Text("midpointObserver uses N=N2 and beta=delta_N2/2. It decodes I by the actual empty law, Ak by the actual startup law G_delta_k, Rd by G_beta, and every other Ri by Fi. G_z=(1-z)Fd+zFf uses the matching dominant branch in both orientations. Saturated startup histories and synchronized dominant histories are within epsilon of this one midpoint; all other queried histories are exact. Pure witnesses 0,1,1B,3,0B have masses 1/5,1/5,p/5,1/5,r/5. Every transient witness B^(k+1) is positive. Thus every charged label belongs to this same actual reached image.")),
            Paragraph(Text("A collision i<j on the startup orbit recurs at i+ell(j-i), by the same total B update. Each corresponding history is finite and positive. At each finite H, triangles bound the fixed decoder at the collision state by epsilon+delta_(i+ell(j-i)) from the dominant law. Geometric decay then constrains that fixed decoder within epsilon, and the horizon supremum forces delta_i<=2 epsilon. No infinite all-B query, decoder continuity, assumed profile completion or supplied age occurs.")),
            Paragraph(Text("For after-read-only unequal observers, initialization cannot be a synchronized reached state: append a positive B in both contexts and compare the first-read half-mixture with pure 2 or 4 at distance one half. It cannot be a startup state either, because that makes startup zero recur and forces delta_0=1/2<=2 epsilon. This argument never queries the initial decoder and adds initialization to the same five-plus-N2 reached injection.")),
            Paragraph(Text("The equality post-read carrier is State+Unit, whose Unit label has the half-mixture law and a B self-loop. It initializes directly at that label. The initialized equality carrier is Option(State+Unit), with an additional I decoded by the actual empty law. Every singleton resets either machine to its pure label. The separate r=p+q argument gives exact predictions for all queried positive histories, and the independent injections give six post-read-only total states or seven initialized total states. Both machines reach exactly six labels after reads. These minima hold at epsilon=0 and at every nonnegative tolerance with 2 epsilon<kappa; no unequal theorem is specialized at theta=1.")),
            Definition("Observer.run","Observer run",
                Observers(All("h",History,EqF(Run(O,Hh),Call("foldl",Call("update",O),Initial(O),Hh))))),
            Definition("Observer.Coherent","Observer coherent",
                Observers(IffF(CoherentObserver(O),All("z",Ztype,Coherent(Decode(O,Zz)))))),
            Definition("Observer.Accurate","Observer accurate",
                Parameters(All("epsilon",Real,Observers(All("queryEmpty",Bool,IffF(Accuracy(O,Flag),All("h",History,ImpliesF(Pos(Mass(Hh)),ImpliesF(Query(Flag,Hh),All("H",Nat,Le(Tv(Actual(Hh),Decode(O,Run(O,Hh)),Horizon),Epsilon))))))))))),
            Definition("Observer.Reached","Observer reached",
                Parameters(Observers(All("z",Ztype,IffF(Member(Zz,Reached(O)),Some("h",History,Conj(Nonempty(Hh),Pos(Mass(Hh)),EqF(Run(O,Hh),Zz)))))))),
            Entry("run_snoc","Run snoc",
                Observers(All("h",History,All("y",Visible,EqF(Run(O,Append(Hh,Singleton(Y))),Update(O,Run(O,Hh),Y)))))),
            Entry("actual_coherent","Actual coherent",
                Admits(All("h",History,ImpliesF(Pos(Mass(Hh)),Coherent(Actual(Hh)))))),
            Entry("accurate_profile","Accurate profile",
                Parameters(All("epsilon",Real,Observers(All("queryEmpty",Bool,ImpliesF(Accuracy(O,Flag),All("h",History,ImpliesF(Conj(Pos(Mass(Hh)),Query(Flag,Hh)),Le(Distance(Actual(Hh),Decode(O,Run(O,Hh))),Epsilon))))))))),
            Entry("common_state_distance","Common state distance",
                Parameters(All("epsilon",Real,Observers(All("queryEmpty",Bool,ImpliesF(Accuracy(O,Flag),All("h",History,All("t",History,ImpliesF(Conj(Pos(Mass(Hh)),Pos(Mass(T)),Query(Flag,Hh),Query(Flag,T),EqF(Run(O,Hh),Run(O,T))),Le(Distance(Actual(Hh),Actual(T)),Twice)))))))))),
            Entry("dominant_successor","Dominant successor",
                Parameters(EqF(Call("pureBSuccessor",DominantState),DominantState))),
            Entry("dominant_law","Dominant law",
                Parameters(EqF(Pure(DominantState),Dominant))),
            Entry("sharp_source_step","Sharp source step",
                All("d",State,All("N",Nat,ImpliesF(EqF(Call("pureBSuccessor",Dd),Dd),All("z",Tag,All("y",Visible,EqF(Call("sharpUpdate",Dd,N,Call("encodeSource",Dd,N,Zz),Y),Call("encodeSource",Dd,N,Call("sourceUpdate",Zz,Y))))))))),
            Entry("sharp_source_run","Sharp source run",
                All("d",State,All("N",Nat,ImpliesF(EqF(Call("pureBSuccessor",Dd),Dd),All("h",History,EqF(Call("foldSharp",Dd,N,Hh),Call("encodeSource",Dd,N,Call("sourceRun",Hh)))))))),
            Entry("midpoint_run","Midpoint run",
                Parameters(All("epsilon",Real,All("h",History,EqF(Run(Midpoint,Hh),Call("encodeSource",DominantState,Ntwo,Call("sourceRun",Hh))))))),
            Entry("midpoint_decoder_coherent","Midpoint decoder coherent",
                SmallError(CoherentObserver(Midpoint))),
            Entry("actual_pure_law","Actual pure law",
                Parameters(All("h",History,ImpliesF(Nonempty(Hh),All("i",State,ImpliesF(EqF(Call("acquiredPosterior",P,Q,R,Hh),Call("pureVector",I)),EqF(Actual(Hh),Pure(I)))))))),
            Entry("midpoint_observer_accuracy","Midpoint observer accuracy",
                SmallError(Accuracy(Midpoint,TrueValue))),
            Entry("sharp_state_card","Sharp state card",
                All("N",Nat,EqF(Card(Call("SharpState",N)),Add(D(6),N)))),
            Entry("midpoint_reached_iff","Midpoint reached iff",
                Admits(All("epsilon",Real,All("z",Call("SharpState",Ntwo),IffF(Member(Zz,Reached(Midpoint)),Ne(Zz,None)))))),
            Entry("midpoint_observer_reachability","Midpoint observer reachability",
                Admits(All("epsilon",Real,Conj(EqF(Reached(Midpoint),Call("notNoneSet")),EqF(ReachCard(Midpoint),Add(D(5),Ntwo)),EqF(Card(Call("SharpState",Ntwo)),Add(D(6),Ntwo)))))),
            Entry("fold_replicate","Fold replicate",
                All("Z",Universe,All("u",Arrow(Ztype,Visible,Ztype),All("z",Ztype,All("n",Nat,EqF(Call("foldl",U,Zz,Call("replicate",Nn,Bsymbol)),Call("iterate",Call("Bstep",U),Nn,Zz))))))),
            Entry("startup_shift","Startup shift",
                Observers(All("i",Nat,All("n",Nat,EqF(StartupState(O,Add(I,Nn)),Call("iterate",Call("BstepObserver",O),Nn,StartupState(O,I))))))),
            Entry("startup_collision_recurrence","Startup collision recurrence",
                Observers(All("i",Nat,All("j",Nat,ImpliesF(Conj(Less(I,J),EqF(StartupState(O,I),StartupState(O,J))),All("ell",Nat,EqF(StartupState(O,Add(I,Mul(Ell,Sub(J,I)))),StartupState(O,I)))))))),
            Entry("recurring_decoder_dominant_bound","Recurring decoder dominant bound",
                Unequal(All("epsilon",Real,Observers(All("queryEmpty",Bool,ImpliesF(Accuracy(O,Flag),All("i",Nat,All("j",Nat,ImpliesF(Conj(Less(I,J),EqF(StartupState(O,I),StartupState(O,J))),All("H",Nat,Le(Tv(Decode(O,StartupState(O,I)),Dominant,Horizon),Epsilon))))))))))),
            Entry("startup_collision_forces_cutoff","Startup collision forces cutoff",
                Unequal(All("epsilon",Real,Observers(All("queryEmpty",Bool,ImpliesF(Conj(CoherentObserver(O),Accuracy(O,Flag)),All("i",Nat,All("j",Nat,ImpliesF(Conj(Less(I,J),EqF(StartupState(O,I),StartupState(O,J))),Le(Delta(I),Twice)))))))))),
            Entry("pure_witness_actual","Pure witness actual",
                Admits(All("i",State,Conj(Nonempty(Witness(I)),Pos(Mass(Witness(I))),EqF(Actual(Witness(I)),Pure(I)))))),
            Entry("charged_reached","Charged reached",
                Admits(Observers(All("N",Nat,All("t",Sum(State,Call("Fin",N)),Member(Call("chargedState",O,N,T),Reached(O))))))),
            Entry("unequal_charged_injective","Unequal charged injective",
                SmallError(Observers(All("queryEmpty",Bool,ImpliesF(Conj(CoherentObserver(O),Accuracy(O,Flag)),Call("Injective",Call("chargedState",O,Ntwo))))))),
            Entry("initial_B_half","Initial b half",
                Admits(EqF(Actual(Singleton(Bsymbol)),Half))),
            Entry("half_pure_B_distance","Half pure b distance",
                Admits(All("i",State,EqF(Distance(Half,Pure(Call("pureBSuccessor",I))),Div(D(1),D(2)))))),
            Entry("postread_initialization_extra_state","Postread initialization extra state",
                Unequal(All("epsilon",Real,ImpliesF(Less(Twice,Kappa),Observers(All("queryEmpty",Bool,ImpliesF(Conj(CoherentObserver(O),Accuracy(O,Flag)),All("h",History,ImpliesF(Conj(Nonempty(Hh),Pos(Mass(Hh))),Ne(Initial(O),Run(O,Hh))))))))))),
            Entry("unequal_initialized_injective","Unequal initialized injective",
                SmallError(Observers(All("queryEmpty",Bool,ImpliesF(Conj(CoherentObserver(O),Accuracy(O,Flag)),Call("Injective",Call("initializedCharged",O,Ntwo))))))),
            Entry("universal_unequal_lower_bound","Universal unequal lower bound",
                SmallError(Observers(All("queryEmpty",Bool,ImpliesF(Conj(CoherentObserver(O),Accuracy(O,Flag)),UnequalBounds(O))),true))),
            Entry("equality_project_step","Equality project step",
                All("z",Tag,All("y",Visible,EqF(Call("equalityUpdate",Call("equalityProject",Zz),Y),Call("equalityProject",Call("sourceUpdate",Zz,Y)))))),
            Entry("equality_initialized_step","Equality initialized step",
                All("z",Tag,All("y",Visible,EqF(Call("equalityInitializedUpdate",Call("equalityInitializedProject",Zz),Y),Call("equalityInitializedProject",Call("sourceUpdate",Zz,Y)))))),
            Entry("equality_run_invariants","Equality run invariants",
                Parameters(All("h",History,Conj(EqF(Run(EqPost,Hh),Call("equalityProject",Call("sourceRun",Hh))),EqF(Run(EqInit,Hh),Call("equalityInitializedProject",Call("sourceRun",Hh))))))),
            Entry("equality_decoder_coherent","Equality decoder coherent",
                Admits(Conj(CoherentObserver(EqPost),CoherentObserver(EqInit)))),
            Entry("equality_observers_exact","Equality observers exact",
                Equality(Conj(ExactPost,ExactInit))),
            Entry("equality_observer_accuracy","Equality observer accuracy",
                Equality(All("epsilon",Real,ImpliesF(Le(D(0),Epsilon),Conj(Accuracy(EqPost,FalseValue),Accuracy(EqInit,TrueValue)))))),
            Entry("equality_reached_all","Equality reached all",
                Admits(Conj(EqF(Reached(EqPost),Call("univ")),EqF(Reached(EqInit),Call("notNoneSet"))))),
            Entry("half_pure_separation","Half pure separation",
                Admits(All("i",State,Le(Kappa,Distance(Half,Pure(I)))))),
            Entry("equality_charged_reached","Equality charged reached",
                Admits(Observers(All("z",EqState,Member(Call("equalityCharged",O,Zz),Reached(O)))))),
            Entry("equality_charged_injective","Equality charged injective",
                Admits(All("epsilon",Real,ImpliesF(Less(Twice,Kappa),Observers(All("queryEmpty",Bool,ImpliesF(Accuracy(O,Flag),Call("Injective",Call("equalityCharged",O))))))))),
            Entry("equality_initialized_injective","Equality initialized injective",
                Admits(All("epsilon",Real,ImpliesF(Less(Twice,Kappa),Observers(ImpliesF(Accuracy(O,TrueValue),Call("Injective",Call("equalityInitializedCharged",O)))))))),
            Entry("universal_equality_lower_bounds","Universal equality lower bounds",
                Admits(All("epsilon",Real,ImpliesF(Less(Twice,Kappa),Observers(Conj(ImpliesF(Accuracy(O,FalseValue),EqualityBounds(O,D(6))),ImpliesF(Accuracy(O,TrueValue),EqualityBounds(O,D(7)))),true))))),
            Entry("equality_observer_cardinalities","Equality observer cardinalities",
                Admits(Conj(EqF(Card(EqState),D(6)),EqF(Card(Call("Option",EqState)),D(7)),EqF(ReachCard(EqPost),D(6)),EqF(ReachCard(EqInit),D(6))))),
            Entry("sharp_initialized_common_decoder","Sharp initialized common decoder",
                OriginalSmall(Conj(CoherentObserver(Midpoint),Accuracy(Midpoint,TrueValue),EqF(Card(Call("SharpState",Ntwo)),Add(D(6),Ntwo)),EqF(ReachCard(Midpoint),Add(D(5),Ntwo)),Observers(ImpliesF(CoherentObserver(O),ImpliesF(Accuracy(O,TrueValue),UnequalBounds(O))),true)))),
            Entry("sharp_postread_reached_common_decoder","Sharp postread reached common decoder",
                OriginalSmall(Conj(CoherentObserver(Midpoint),Accuracy(Midpoint,FalseValue),EqF(ReachCard(Midpoint),Add(D(5),Ntwo)),Observers(ImpliesF(CoherentObserver(O),ImpliesF(Accuracy(O,FalseValue),Le(Add(D(5),Ntwo),ReachCard(O)))),true)))),
            Entry("postread_only_unequal_minimum","Postread only unequal minimum",
                OriginalSmall(Conj(CoherentObserver(Midpoint),Accuracy(Midpoint,FalseValue),EqF(Card(Call("SharpState",Ntwo)),Add(D(6),Ntwo)),EqF(ReachCard(Midpoint),Add(D(5),Ntwo)),Observers(ImpliesF(CoherentObserver(O),ImpliesF(Accuracy(O,FalseValue),UnequalBounds(O))),true)))),
            Entry("equality_observer_minima","Equality observer minima",
                Equality(All("epsilon",Real,ImpliesF(Conj(Le(D(0),Epsilon),Less(Twice,Kappa)),Conj(CoherentObserver(EqInit),CoherentObserver(EqPost),Accuracy(EqInit,TrueValue),Accuracy(EqPost,FalseValue),EqF(Card(Call("Option",EqState)),D(7)),EqF(Card(EqState),D(6)),EqF(ReachCard(EqInit),D(6)),EqF(ReachCard(EqPost),D(6)),ExactInit,ExactPost,Observers(Conj(ImpliesF(CoherentObserver(O),ImpliesF(Accuracy(O,TrueValue),EqualityBounds(O,D(7)))),ImpliesF(CoherentObserver(O),ImpliesF(Accuracy(O,FalseValue),EqualityBounds(O,D(6))))),true)))))))));

    private static DocumentBlock.Describe Entry(string name,string title,Formula formula) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').Replace('.','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModeAutonomousSharpCount."+name),
            H(title),StatementSource.FromAuthor(Disp(formula)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(Note(name)))),DescribeRole.Theorem);
    private static DocumentBlock Definition(string name,string title,Formula formula) =>
        Paragraph(Text(title+": "),Math(Disp(formula)));
    private static string Note(string name) => name switch {
        "run_snoc" => "An appended symbol applies the same total update to the current retained state.",
        "actual_coherent" => "Positive finite histories induce normalized actual laws with final-symbol consistency.",
        "accurate_profile" => "The uniform finite-horizon error bound also bounds its supremum.",
        "common_state_distance" => "One shared decoder and two finite-horizon triangles bound the true-law distance by twice epsilon.",
        "dominant_successor" => "Both possible dominant labels remain at the same pure label under B.",
        "dominant_law" => "The selected dominant state uses its matching pure future law.",
        "sharp_source_step" => "Every visible read preserves the projection, including the saturated boundary and impossible extensions.",
        "sharp_source_run" => "The total-update projection is preserved along every finite word.",
        "midpoint_run" => "The run is a function of the acquired word through one retained-state update.",
        "midpoint_decoder_coherent" => "Every label has one normalized, marginally coherent complete-law decoder.",
        "actual_pure_law" => "A nonempty boundary with point-mass posterior has that point mass's pure future law.",
        "midpoint_observer_accuracy" => "The actual startup tail and dominant pure state use the same midpoint, uniformly over all actual histories and horizons.",
        "sharp_state_card" => "One initialization label, five pure labels and N transient labels give six plus N.",
        "midpoint_reached_iff" => "Every Some label is actually reached and no positive nonempty word reaches None.",
        "midpoint_observer_reachability" => "The actual image has five plus N2 labels, while the total carrier has six plus N2.",
        "fold_replicate" => "A finite repeated input is an iterate of the corresponding total update.",
        "startup_shift" => "The startup index increases by the number of appended B reads.",
        "startup_collision_recurrence" => "A collision fixes the retained state at every finite repetition of its gap.",
        "recurring_decoder_dominant_bound" => "Finite-horizon triangles and geometric decay constrain one fixed decoder; no infinite all-B query is used.",
        "startup_collision_forces_cutoff" => "The horizon supremum forces the non-strict delta_i threshold without restricting the decoder to mixtures.",
        "pure_witness_actual" => "The five exhibited histories are nonempty, positive and have their matching pure laws.",
        "charged_reached" => "The pure and transient witnesses belong to one actual reached image.",
        "unequal_charged_injective" => "Pre-cutoff startup collisions are forbidden, and each pure law is separate from every charged startup law.",
        "initial_B_half" => "The first acquired B has equal posterior weights on the two hidden B branches.",
        "half_pure_B_distance" => "Either pure B successor is at complete-law distance one half from the first-read half-mixture.",
        "postread_initialization_extra_state" => "Positive appended B separates synchronized states from initialization, and recurrence excludes startup states, without querying the initial decoder.",
        "unequal_initialized_injective" => "Initialization adds to the same actual pure/transient injection.",
        "universal_unequal_lower_bound" => "All arbitrary finite deterministic competitors obey both lower counts under either query convention.",
        "equality_project_step" => "Start and every startup tag share the B-fixed half-mixture label in the post-read carrier.",
        "equality_initialized_step" => "The initialized carrier preserves a separate initial label and collapses all startup tags.",
        "equality_run_invariants" => "Both total updates preserve their source-tag projection along all finite words.",
        "equality_decoder_coherent" => "The actual empty, pure and half-mixture profiles are coherent.",
        "equality_observers_exact" => "Equality of the holding probabilities makes both machines exact on their entire queried actual domains.",
        "equality_observer_accuracy" => "Exact law reconstruction gives zero TV error at every future horizon.",
        "equality_reached_all" => "All six post-read labels have actual witnesses; the initialized label is additional.",
        "half_pure_separation" => "The half-mixture is separated from all five pure laws without excluding p=q.",
        "equality_charged_reached" => "The five pure witnesses and first B give six actual reached states.",
        "equality_charged_injective" => "Six separated actual laws require six distinct retained configurations.",
        "equality_initialized_injective" => "The queryable empty law is separate from all six charged post-read laws.",
        "universal_equality_lower_bounds" => "The independent equality injections yield six post-read-only or seven initialized total states, including tolerance zero.",
        "equality_observer_cardinalities" => "The carriers have six and seven labels and both post-read images have six.",
        "sharp_initialized_common_decoder" => "The original source assumptions derive an attainable six-plus-N2 total and five-plus-N2 reached minimum for a common coherent decoder.",
        "sharp_postread_reached_common_decoder" => "With no empty query the exact reached minimum is still five plus N2.",
        "postread_only_unequal_minimum" => "Initialization still requires an additional total configuration, although it is never queried.",
        "equality_observer_minima" => "The separate equality construction gives seven initialized or six post-read-only total configurations, exactly and at the stipulated tolerance.",
        _ => throw new System.ArgumentException("Unknown mathematical declaration.")
    };
    private static Formula Call(string name,params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name),[..args]);
    private static Formula All(string name,Formula type,Formula body) => Seq(Open,Forall,Sp,F.Id(name),Colon,Sp,type,Comma,Esc,body,Close);
    private static Formula Some(string name,Formula type,Formula body) => Seq(Open,Exists,Sp,F.Id(name),Colon,Sp,type,Comma,Esc,body,Close);
    private static Formula Parameters(Formula body) => All("p",Real,All("q",Real,All("r",Real,body)));
    private static Formula Admits(Formula body) => Parameters(ImpliesF(Call("admissible",P,Q,R),body));
    private static Formula Unequal(Formula body) => Admits(ImpliesF(Ne(A,Bhold),body));
    private static Formula Equality(Formula body) => Admits(ImpliesF(EqF(R,Add(P,Q)),body));
    private static Formula SmallError(Formula body) => Unequal(All("epsilon",Real,ImpliesF(Conj(Pos(Twice),Less(Twice,Kappa)),body)));
    private static Formula OriginalSmall(Formula body) => Admits(All("epsilon",Real,ImpliesF(Conj(Ne(R,Add(P,Q)),Pos(Twice),Less(Twice,Kappa)),body)));
    private static Formula Observers(Formula body,bool finite=false) => All("Z",Universe,
        finite ? All("inst",Call("Fintype",Ztype),All("O",Call("Observer",Ztype),body)) : All("O",Call("Observer",Ztype),body));
    private static Formula EqF(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Ne(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Le(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Less(Formula a,Formula b) => Seq(a,Sp,Lt,Sp,b);
    private static Formula Pos(Formula a) => Less(D(0),a);
    private static Formula AndF(Formula a,Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Conj(params Formula[] xs) => xs.Reverse().Aggregate((a,b)=>AndF(b,a));
    private static Formula OrF(Formula a,Formula b) => Seq(Open,a,Sp,Lor,Sp,b,Close);
    private static Formula ImpliesF(Formula a,Formula b) => Seq(Open,a,Sp,Rightarrow,Sp,b,Close);
    private static Formula IffF(Formula a,Formula b) => Seq(Open,a,Sp,Iff,Sp,b,Close);
    private static Formula Member(Formula a,Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula Add(Formula a,Formula b) => Seq(Open,a,Plus,b,Close);
    private static Formula Sub(Formula a,Formula b) => Seq(Open,a,Minus,b,Close);
    private static Formula Mul(Formula a,Formula b) => Seq(Open,a,Star,b,Close);
    private static Formula Div(Formula a,Formula b) => new Formula.Fraction(a,b);
    private static Formula Arrow(params Formula[] types) => types.Reverse().Aggregate((a,b)=>Seq(b,Sp,To,Sp,a));
    private static Formula Sum(Formula a,Formula b) => Call("Sum",a,b);
    private static Formula Singleton(Formula y) => Call("singleton",y);
    private static Formula Append(Formula h,Formula t) => Call("append",h,t);
    private static Formula Nonempty(Formula h) => Ne(h,Call("nil"));
    private static Formula Query(Formula flag,Formula h) => OrF(EqF(flag,TrueValue),Nonempty(h));
    private static Formula Run(Formula o,Formula h) => Call("run",o,h);
    private static Formula Initial(Formula o) => Call("initial",o);
    private static Formula Update(Formula o,Formula z,Formula y) => Call("update",o,z,y);
    private static Formula Decode(Formula o,Formula z) => Call("decoder",o,z);
    private static Formula Coherent(Formula f) => Call("CoherentProfile",f);
    private static Formula CoherentObserver(Formula o) => Call("CoherentObserver",o);
    private static Formula Accuracy(Formula o,Formula flag) => Call("Accurate",o,P,Q,R,Epsilon,flag);
    private static Formula Reached(Formula o) => Call("Reached",o,P,Q,R);
    private static Formula Card(Formula t) => Call("FintypeCard",t);
    private static Formula ReachCard(Formula o) => Call("NatCard",Reached(o));
    private static Formula UnequalBounds(Formula o) => Conj(Le(Add(D(6),Ntwo),Card(Ztype)),Le(Add(D(5),Ntwo),ReachCard(o)));
    private static Formula EqualityBounds(Formula o,Formula total) => Conj(Le(total,Card(Ztype)),Le(D(6),ReachCard(o)));
    private static Formula ExactPost => All("h",History,ImpliesF(Nonempty(Hh),ImpliesF(Pos(Mass(Hh)),EqF(Decode(EqPost,Run(EqPost,Hh)),Actual(Hh)))));
    private static Formula ExactInit => All("h",History,ImpliesF(Pos(Mass(Hh)),EqF(Decode(EqInit,Run(EqInit,Hh)),Actual(Hh))));
    private static Formula Pure(Formula i) => Call("pureLaw",P,Q,R,i);
    private static Formula Actual(Formula h) => Call("actualFutureWordWeight",P,Q,R,h);
    private static Formula Mass(Formula h) => Call("historyMass",P,Q,R,h);
    private static Formula Witness(Formula i) => Call("pureWitness",i);
    private static Formula StartupState(Formula o,Formula k) => Call("startupState",o,k);
    private static Formula Delta(Formula k) => Call("minority",Call("theta",P,Q,R),k);
    private static Formula Tv(Formula f,Formula g,Formula h) => Call("TV",Call("at",f,h),Call("at",g,h));
    private static Formula Distance(Formula f,Formula g) => Call("profileDistance",f,g);
    private static Formula Real => Seq(Mathbb,Grp(F.Id("R")));
    private static Formula Nat => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Universe => F.Id("Type");
    private static Formula State => F.Id("State"); private static Formula Visible => F.Id("Visible");
    private static Formula Tag => F.Id("SourceTag"); private static Formula Bool => F.Id("Bool");
    private static Formula History => Call("List",Visible);
    private static Formula EqState => Sum(State,F.Id("Unit"));
    private static Formula P => F.Id("p"); private static Formula Q => F.Id("q"); private static Formula R => F.Id("r");
    private static Formula O => F.Id("O"); private static Formula Ztype => F.Id("Z"); private static Formula Zz => F.Id("z");
    private static Formula Hh => F.Id("h"); private static Formula T => F.Id("t"); private static Formula Y => F.Id("y");
    private static Formula I => F.Id("i"); private static Formula J => F.Id("j"); private static Formula Ell => F.Id("ell");
    private static Formula N => F.Id("N"); private static Formula Nn => F.Id("n"); private static Formula Dd => F.Id("d"); private static Formula U => F.Id("u");
    private static Formula Horizon => F.Id("H"); private static Formula Epsilon => F.Id("epsilon"); private static Formula Flag => F.Id("queryEmpty");
    private static Formula Twice => Mul(D(2),Epsilon);
    private static Formula A => Call("a",P,Q); private static Formula Bhold => Call("b",R);
    private static Formula Kappa => Call("kappa",P,Q,R); private static Formula Ntwo => Call("N2",P,Q,R,Epsilon);
    private static Formula DominantState => Call("dominantState",P,Q,R); private static Formula Dominant => Call("dominantLaw",P,Q,R);
    private static Formula Half => Call("mixtureLaw",P,Q,R,Div(D(1),D(2)));
    private static Formula Midpoint => Call("midpointObserver",P,Q,R,Epsilon);
    private static Formula EqPost => Call("equalityPostreadObserver",P,Q,R);
    private static Formula EqInit => Call("equalityInitializedObserver",P,Q,R);
    private static Formula Bsymbol => F.Id("B"); private static Formula None => F.Id("None");
    private static Formula TrueValue => F.Id("true"); private static Formula FalseValue => F.Id("false");
}
