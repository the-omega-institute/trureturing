using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Prediction;

internal sealed class FiveModeSelfGeneratedLawsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Same-update generated laws, exact uniform errors and attained initialized finite-carrier minimum bounds.",
        H("Five Mode Self Generated Laws"),
        Blocks(
            Paragraph(Text("The source is the literal five-mode model: p,q,r>0 and p+q+r<1, a=1-p-q, b=1-r and c=1-p-q-r. This module treats a!=b in both holding orientations, including p=q. The hidden carrier is Fin 5. Visible symbols are Fin 4 with B=2; Lean order is (0,1,B,3), while the source prose uses (0,1,3,B).")),
            Paragraph(Text("Every source-legal finite history has positive actual historyMass. Empty history is included and predicts Y0; after a nonempty acquired history, the future begins after its last acquired read. Every natural horizon is included. H=0 has its unique normalized empty word and TV zero.")),
            Paragraph(Text("GeneratedObserver emits nonnegative normalized rows at every complete carrier configuration, including configurations used only by hypothetical generated words. The same total U defines retention and every product decoder. A legal actual input can have forecast row weight zero; all singleton overwrites remain defined and the actual-history accuracy guarantee uses actual source legality.")),
            Paragraph(Text("For positive N and k:Fin N put m=N-k, T_j=a^j+b^j, u=min(a,b), v=max(a,b), theta=u/v and delta_j=theta^j/(1+theta^j)=u^j/T_j. The actual laws agree through horizon m. At longer horizons only the chronological prefix List.replicate m B contributes to their signed difference. Its factor is T_N/T_k, followed by the actual startup-N residual versus the dominant pure residual. Complete word sums include impossible and zero-weight words.")),
            Paragraph(Text("The exact transient finite error is zero for H<=m and (T_N/T_k)*delta_N*(1-u^(H-m)) for H>m. Its all-horizon supremum is (T_N/T_k)*delta_N=u^N/T_k<=delta_N. The initialized B branch has mass 2/5 and enters A0, so initialized finite error is zero through N+1 and (u^N/5)*(1-u^(H-N-1)) thereafter; its exact supremum is u^N/5<=delta_N.")),
            Paragraph(Text("Actual source classification exhausts empty history, startup k<N at Ak, startup k>=N at the dominant pure label with delta_k<=delta_N, and singleton-containing pure histories. The actual source fold and the retained fold use the matching total update, giving the uniform all-history bound.")),
            Paragraph(Text("With 0<2 epsilon<kappa, N1=cutoff(theta,epsilon) is the first non-strict threshold and N2=cutoff(theta,2 epsilon). Ties are allowed. The constructed full carrier has 6+N1 configurations. Every competing finite normalized generator derives coherence and the original common-law lower bound 6+N2 under its original accuracy condition.")),
            Paragraph(Text("Attainable n means that an initialized accurate normalized generator exists on Fin n. Exact equivalence transport connects this predicate to every finite carrier and counts every configuration. Nonemptiness comes from the actual constructed law. Nat least-element existence gives an attained minimum with 6+N2<=minimum<=6+N1; coincident cutoffs give minimum=6+N1.")),
            Paragraph(Text("The formulas use Words(H) for the complete Fin H to Visible carrier, so zero-weight and impossible words remain included; Law abbreviates cutoffLaw, Startup abbreviates startupLaw, and Enc(k) is encodeSource(d,N,startup k). Distance is the all-natural-horizon profileDistance, TV is the finite half-L1 totalVariation, and Min is the proof-independent least attainable initialized size under the displayed small-error premises. differenceProfile(F,G)(H,w) is F(H,w)-G(H,w), and atHorizon(F,H) is F H. A Fin N index in T or N-k means its natural value. Accurate(toObserver(g),p,q,r,epsilon,true) is the exact actual-history and all-natural-horizon guarantee; proof arguments are suppressed. Missing statement projections are explicit gaps; their declaration handles still bind to the current compiled Lean source.")),
            Paragraph(Text("The stronger unequal optimum when N1>N2 remains open. Equality a=b, its separate seven-state realization and minimum, and the actual midpoint conditional-tail obstruction belong to their separate source obligations. No unequal logarithmic cutoff is evaluated at theta=1.")),
            Entry("generatedLaw","generatedLaw",DescribeRole.Definition,"For every carrier, total U, real row map g, configuration, natural horizon and complete visible word: horizon zero has weight one; the next-symbol weight multiplies the law at U(z,y)."),
            Entry("GeneratedObserver","GeneratedObserver",DescribeRole.Definition,"A carrier has one initial configuration, a total symbol update, and a nonnegative row of total mass one at every configuration."),
            Entry("GeneratedObserver.toObserver","GeneratedObserver toObserver",DescribeRole.Definition,"The retained fold and every hypothetical generated word use the same total update; the decoder is generatedLaw of this update and its rows."),
            Entry("generated_cons","generated cons",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_nonnegative","generated nonnegative",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_sum","generated sum",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_final_symbol","generated final symbol",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_coherent","generated coherent",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("one_step_probability","one step probability",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoffRows","cutoffRows",DescribeRole.Definition,"I emits 1/5 at each singleton 0,1,3 and 2/5 at B. Every Ri emits its pure source row. Ak emits the actual one-step law of G_delta_k."),
            Entry("cutoffRows_probability","cutoffRows probability",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoffGenerator","cutoffGenerator",DescribeRole.Definition,"For every admissible unequal source and natural cutoff N, use the complete SharpState N carrier with I as initial state, sharpUpdate of the matching dominant state, and the normalized cutoff rows."),
            Entry("cutoff_row_is_actual","cutoff row is actual",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoff_run_is_actual","cutoff run is actual",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoff_singleton_total","cutoff singleton total",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("actual_startup_B_recurrence","actual startup B recurrence",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("singletonState","singletonState",DescribeRole.Definition,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("nextPure","nextPure",DescribeRole.Definition,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("pure_zero","pure zero",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("pure_cons","pure cons",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("pure_update","pure update",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoffLaw","cutoffLaw",DescribeRole.Definition,"The decoder is precisely the product law of sharpUpdate and cutoffRows, at every carrier configuration and complete word."),
            Entry("pure_generated","pure generated",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("T","T",DescribeRole.Definition,"T_k=a^k+b^k for every natural k."),
            Entry("startupLaw","startupLaw",DescribeRole.Definition,"The actual conditional source future after the finite acquired history B^(k+1)."),
            Entry("T_pos","T pos",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("startup_zero","startup zero",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("startup_B","startup B",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("startup_singleton","startup singleton",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("startup_B_row","startup B row",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cutoff_startup_row","cutoff startup row",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_startup_B","generated startup B",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("generated_startup_singleton","generated startup singleton",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("cylinder","cylinder",DescribeRole.Definition,"The signed suffix law is placed on the literal chronological all-B prefix; words leaving that prefix have zero signed weight."),
            Entry("cylinder_zero","cylinder zero",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("source_product_localization","source product localization",DescribeRole.Lemma,"For every admissible unequal source, N,k,H with k<=N, and every complete word, startupLaw_k minus the actual generated cutoff law at encodeSource(startup k) equals (T_N/T_k) times the B^(N-k) cylinder of startupLaw_N minus the dominant pure law. Zero-weight words are included."),
            Entry("cylinder_pre","cylinder pre",DescribeRole.Lemma,"A consumed interface for the actual source rows, complete word recurrence and same total update; all quantified parameters and hypotheses are those of the named Lean declaration."),
            Entry("precutoff_agreement","precutoff agreement",DescribeRole.Lemma,"For every k:Fin N, every H<=N-k and every complete word, the actual generated law equals G_delta_k. Horizon zero and the cutoff endpoint are included."),
            Entry("cylinder_abs_sum","cylinder abs sum",DescribeRole.Lemma,"Summing the absolute cylinder weight over every word of length t+m gives the absolute suffix sum over every word of length t."),
            Entry("startup_dominant_finite","startup dominant finite",DescribeRole.Lemma,"The exact finite TV between the actual startup law and the dominant pure law is delta_k times (1-u^H), including H=0."),
            Entry("transient_shift_tv","transient shift tv",DescribeRole.Lemma,"At every residual horizon t, the actual transient TV at horizon t+(N-k) is T_N/T_k times the residual startup-N versus dominant-pure TV."),
            Entry("transient_finite_tv","transient finite tv",DescribeRole.Lemma,"For every admissible unequal source, N, k:Fin N and natural H, actual TV is zero when H<=N-k and is (T_N/T_k)*delta_N*(1-u^(H-(N-k))) otherwise. The half-L1 sum ranges over all words."),
            Entry("transient_profile_distance","transient profile distance",DescribeRole.Lemma,"The genuine supremum over all natural horizons is (T_N/T_k)*delta_N. Every residual horizon is represented by the shifted full horizon N-k+t; the frozen residual profile geometry supplies the reverse inequality."),
            Entry("minority_power_ratio","minority power ratio",DescribeRole.Lemma,"For every admissible unequal source and natural k, delta_k=u^k/T_k in either holding orientation."),
            Entry("T_antitone","T antitone",DescribeRole.Lemma,"For every admissible source and natural k<=N, T_N<=T_k."),
            Entry("transient_gain","transient gain",DescribeRole.Lemma,"The exact transient profile error is u^N/T_k and is at most delta_N."),
            Entry("empty_singleton_cons","empty singleton cons",DescribeRole.Lemma,"For every singleton y in 0,1,3 and every suffix word, the actual initialized joint word weight is 1/5 times its matching pure suffix law."),
            Entry("empty_B_startup","empty B startup",DescribeRole.Lemma,"The actual initialized B branch has mass 2/5 and continues at the actual startup-zero law."),
            Entry("initial_difference","initial difference",DescribeRole.Lemma,"For positive N, initialized singleton differences vanish; the B difference is 2/5 times the actual startup-zero minus cutoff-A0 suffix difference."),
            Entry("initial_succ_tv","initial succ tv",DescribeRole.Lemma,"For positive N, the actual initialized TV at H+1 is 2/5 times the startup-zero transient TV at H."),
            Entry("initial_finite_tv","initial finite tv",DescribeRole.Lemma,"For every positive N and natural H, initialized TV is zero through N+1 and is (u^N/5)*(1-u^(H-N-1)) thereafter. The extra initial B read is included."),
            Entry("initial_profile_distance","initial profile distance",DescribeRole.Lemma,"For every positive N, the initialized all-horizon supremum is exactly u^N/5."),
            Entry("initial_gain_le","initial gain le",DescribeRole.Lemma,"For every positive N, u^N/5<=delta_N."),
            Entry("saturated_profile","saturated profile",DescribeRole.Lemma,"For every actual startup index k>=N, the retained dominant pure label has exact profile error delta_k."),
            Entry("pure_history_exact","pure history exact",DescribeRole.Lemma,"Every nonempty actual history classified as pure i has its actual source law at the retained pure label, without any approximate-forecast support premise."),
            Entry("cutoff_history_profile","cutoff history profile",DescribeRole.Lemma,"For every admissible unequal source, positive N and every actual positive finite history, including empty history, the actual profile error of the same-U cutoff generator is at most delta_N."),
            Entry("cutoff_accuracy","cutoff accuracy",DescribeRole.Lemma,"One generator has the finite-horizon guarantee simultaneously for every actual positive finite history and every natural horizon. Actual legality is measured by historyMass."),
            Entry("N1","N1",DescribeRole.Definition,"N1 is the natural ceiling cutoff(theta,epsilon), using the original non-strict minority threshold."),
            Entry("N1_threshold","N1 threshold",DescribeRole.Lemma,"Under 0<2 epsilon<kappa and unequal holdings, N1 is positive, delta_N1<=epsilon, every earlier index is strict, and all non-strict cutoff ties satisfy the original logarithmic equality."),
            Entry("N1_generator_accuracy","N1 generator accuracy",DescribeRole.Lemma,"The actual normalized generator on the full carrier I plus five pure labels plus N1 transients is uniformly epsilon accurate on every actual finite history and every horizon."),
            Entry("generated_competing_lower","generated competing lower",DescribeRole.Lemma,"Every finite normalized GeneratedObserver with the original actual-history guarantee is coherent and inherits the common-law lower bound 6+N2. No reachability, calibration or forecast-positivity condition is added."),
            Entry("transport","transport",DescribeRole.Definition,"An equivalence of full carrier types transports the initial configuration, total update and every emission row."),
            Entry("transport_law","transport law",DescribeRole.Lemma,"The transported generated law at e(z) equals the original generated law at z at every horizon and word."),
            Entry("transport_run","transport run",DescribeRole.Lemma,"The retained run on every finite visible list transports exactly by e."),
            Entry("transport_accurate","transport accurate",DescribeRole.Lemma,"The complete actual-history accuracy property is preserved under full-carrier equivalence."),
            Entry("Attainable","Attainable",DescribeRole.Definition,"A natural carrier size n is attainable exactly when some normalized GeneratedObserver on Fin n satisfies the original initialized all-history, all-horizon accuracy guarantee."),
            Entry("attainable_constructed","attainable constructed",DescribeRole.Lemma,"The actual N1 cutoff generator transports to Fin(6+N1), proving that this complete carrier size is attainable."),
            Entry("attainable_nonempty","attainable nonempty",DescribeRole.Lemma,"The constructed accurate generator proves nonemptiness of the attainable finite carrier-size predicate."),
            Entry("minimum","minimum",DescribeRole.Definition,"The initialized generated-law minimum is Nat.find of the nonempty attainable carrier-size predicate, rather than a witness size or a lower bound alone."),
            Entry("minimum_attained","minimum attained",DescribeRole.Lemma,"The actual least attainable initialized finite carrier size is itself attained by a normalized GeneratedObserver."),
            Entry("minimum_le","minimum le",DescribeRole.Lemma,"The least attainable initialized finite carrier size is at most every attainable size."),
            Entry("minimum_of_any_carrier","minimum of any carrier",DescribeRole.Lemma,"Every accurately initialized normalized generator on every finite carrier transports to Fin(card Z), so the actual minimum is at most its complete carrier cardinality."),
            Entry("initialized_generated_minimum","initialized generated minimum",DescribeRole.Lemma,"Under all original admissibility, unequal-holding and small-error premises, the actual initialized minimum is attained, is no larger than every attainable size, lies between 6+N2 and 6+N1, and equals 6+N1 when N1=N2."))));

    private static DocumentBlock.Describe Entry(string name,string title,DescribeRole role,string note) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').Replace('.','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/ObserverMemory/Prediction/FiveModeSelfGeneratedLaws."+name.Replace("GeneratedObserver.","")),
            H(title),Presentation(name),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(note))),role);

    private static StatementSource Presentation(string name)
    {
        var formula = FormulaFor(name);
        return formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula));
    }

    private static Formula? FormulaFor(string name) => name switch
    {
        "source_product_localization" => Unequal(Naturals(All("k", Nat,
            Implies(Le(K, N), Horizons(Equal(Sub(Startup(K, H, W), Law(Enc(K), H, W)),
                Mul(Div(T(N), T(K)), Call("cylinder", Sub(N, K),
                    Call("differenceProfile", Call("startupLaw", P, Q, R, N),
                        Call("pureLaw", P, Q, R, Dominant)), H, W)))))))),
        "precutoff_agreement" => Unequal(Transients(Horizons(Implies(Le(H, M),
            Equal(Law(Ak, H, W), Call("orientedMixture", P, Q, R, Delta(K), H, W)))))),
        "transient_shift_tv" => Unequal(Transients(All("t", Nat,
            Equal(TV(StartupProfile(K), LawProfile(Ak), Add(Tt, M)),
                Mul(Gain, TV(StartupProfile(N), PureProfile(Dominant), Tt)))))),
        "transient_finite_tv" => Unequal(Transients(All("H", Nat,
            Equal(TV(StartupProfile(K), LawProfile(Ak), H),
                Call("ifThenElse", Le(H, M), Zero, Mul(Mul(Gain, Delta(N)),
                    Sub(One, Pow(U, Sub(H, M))))))))),
        "transient_profile_distance" => Unequal(Transients(
            Equal(Distance(StartupProfile(K), LawProfile(Ak)), Mul(Gain, Delta(N))))),
        "transient_gain" => Unequal(Transients(And(
            Equal(Mul(Gain, Delta(N)), Div(Pow(U, N), T(K))),
            Le(Mul(Gain, Delta(N)), Delta(N))))),
        "initial_finite_tv" => Unequal(PositiveCutoff(All("H", Nat,
            Equal(TV(EmptyProfile, LawProfile(Initial), H),
                Call("ifThenElse", Le(H, Add(N, One)), Zero,
                    Mul(Div(Pow(U, N), Five), Sub(One, Pow(U, Sub(H, Add(N, One)))))))))),
        "initial_profile_distance" => Unequal(PositiveCutoff(
            Equal(Distance(EmptyProfile, LawProfile(Initial)), Div(Pow(U, N), Five)))),
        "initial_gain_le" => Unequal(PositiveCutoff(Le(Div(Pow(U, N), Five), Delta(N)))),
        "cutoff_history_profile" => Unequal(PositiveCutoff(All("h", History,
            Implies(Pos(Call("historyMass", P, Q, R, Hist)),
                Le(Distance(Actual(Hist), DecodeRun(Hist)), Delta(N)))))),
        "cutoff_accuracy" => Unequal(PositiveCutoff(Accurate(Generator(N), Delta(N)))),
        "N1_generator_accuracy" => Small(Accurate(Generator(NOne), Epsilon)),
        "attainable_constructed" => Small(Attainable(Add(Six, NOne))),
        "attainable_nonempty" => Small(Exists("n", Nat, Attainable(Nn))),
        "minimum_attained" => Small(Attainable(Minimum)),
        "initialized_generated_minimum" => Small(And(Attainable(Minimum),
            All("n", Nat, Implies(Attainable(Nn), Le(Minimum, Nn))),
            Le(Add(Six, NTwo), Minimum), Le(Minimum, Add(Six, NOne)),
            Implies(Equal(NOne, NTwo), Equal(Minimum, Add(Six, NOne))))),
        _ => null,
    };

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Call(string name, params Formula[] arguments) => F.Call(name, arguments);
    private static Formula Equal(Formula left, Formula right) => F.Equal(left, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Pos(Formula value) =>
        new Formula.Relation(Zero, FormulaRelationOperator.LessThan, value);
    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);
    private static Formula And(params Formula[] terms) => terms.Aggregate((left, right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right));
    private static Formula Add(Formula left, Formula right) => F.Add(left, right);
    private static Formula Sub(Formula left, Formula right) => F.Subtract(left, right);
    private static Formula Mul(Formula left, Formula right) => F.Multiply(left, right);
    private static Formula Div(Formula left, Formula right) => new Formula.Fraction(left, right);
    private static Formula Pow(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Unequal(Formula body) => All("p", Real, All("q", Real, All("r", Real,
        Implies(And(Call("admissible", P, Q, R), F.NotEqual(Call("a", P, Q), Call("b", R))), body))));
    private static Formula Small(Formula body) => Unequal(All("epsilon", Real,
        Implies(And(Pos(Mul(Two, Epsilon)),
            new Formula.Relation(Mul(Two, Epsilon), FormulaRelationOperator.LessThan,
                Call("kappa", P, Q, R))), body)));
    private static Formula Naturals(Formula body) => All("N", Nat, body);
    private static Formula PositiveCutoff(Formula body) => Naturals(Implies(Pos(N), body));
    private static Formula Transients(Formula body) => Naturals(All("k", Call("Fin", N), body));
    private static Formula Horizons(Formula body) => All("H", Nat, All("w", Call("Words", H), body));
    private static Formula T(Formula k) => Call("T", P, Q, R, k);
    private static Formula Delta(Formula k) => Call("minority", Call("theta", P, Q, R), k);
    private static Formula Startup(Formula k, Formula horizon, Formula word) =>
        Call("startupLaw", P, Q, R, k, horizon, word);
    private static Formula Law(Formula state, Formula horizon, Formula word) =>
        Call("cutoffLaw", P, Q, R, N, state, horizon, word);
    private static Formula Enc(Formula k) => Call("encodeSource", Dominant, N, Call("startup", k));
    private static Formula StartupProfile(Formula k) => Call("startupLaw", P, Q, R, k);
    private static Formula PureProfile(Formula i) => Call("pureLaw", P, Q, R, i);
    private static Formula LawProfile(Formula state) => Call("cutoffLaw", P, Q, R, N, state);
    private static Formula Distance(Formula source, Formula generated) => Call("profileDistance", source, generated);
    private static Formula TV(Formula source, Formula generated, Formula horizon) =>
        Call("totalVariation", Call("atHorizon", source, horizon), Call("atHorizon", generated, horizon));
    private static Formula Generator(Formula cutoff) => Call("cutoffGenerator", P, Q, R, cutoff);
    private static Formula Accurate(Formula observer, Formula error) =>
        Call("Accurate", Call("toObserver", observer), P, Q, R, error, Call("true"));
    private static Formula Actual(Formula history) => Call("actualFutureWordWeight", P, Q, R, history);
    private static Formula DecodeRun(Formula history) => Call("decoder", Call("toObserver", Generator(N)),
        Call("run", Call("toObserver", Generator(N)), history));
    private static Formula Attainable(Formula size) => Call("Attainable", P, Q, R, Epsilon, size);
    private static Formula P => F.Id("p");
    private static Formula Q => F.Id("q");
    private static Formula R => F.Id("r");
    private static Formula N => F.Id("N");
    private static Formula K => F.Id("k");
    private static Formula H => F.Id("H");
    private static Formula W => F.Id("w");
    private static Formula Hist => F.Id("h");
    private static Formula Tt => F.Id("t");
    private static Formula Nn => F.Id("n");
    private static Formula Epsilon => F.Id("epsilon");
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula History => Call("List", Call("Visible"));
    private static Formula U => Call("min", Call("a", P, Q), Call("b", R));
    private static Formula M => Sub(N, K);
    private static Formula Gain => Div(T(N), T(K));
    private static Formula Ak => Call("some", Call("inr", K));
    private static Formula Initial => Call("none");
    private static Formula EmptyProfile => Call("emptyLaw", P, Q, R);
    private static Formula Dominant => Call("dominantState", P, Q, R);
    private static Formula NOne => Call("N1", P, Q, R, Epsilon);
    private static Formula NTwo => Call("N2", P, Q, R, Epsilon);
    private static Formula Minimum => Call("minimum", P, Q, R, Epsilon);
    private static Formula Zero => F.Num(0);
    private static Formula One => F.Num(1);
    private static Formula Two => F.Num(2);
    private static Formula Five => F.Num(5);
    private static Formula Six => F.Num(6);
}
