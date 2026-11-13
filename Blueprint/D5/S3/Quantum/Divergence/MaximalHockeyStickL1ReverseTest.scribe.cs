using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickL1ReverseTestDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickL1ReverseTest.";
    private static Formula Matrix => Call("Matrix", Id("n"), Id("n"), Call("Complex"));
    private static Formula Cost => Call("closedPerspectiveCost", Id("h"), Id("mu"), Id("p"), Id("q"));
    private static Formula Gamma(Formula v) => At(Id("Gamma"), v);
    private static Formula Input(string v) => Call("ComplexToLone", Id(v), Id("mu"));
    private static Formula Convex => Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f"));
    private static Formula FiniteCost => Call("Ne", Cost, Call("Top"));
    private static Formula PointCost(Formula p, Formula q) => Call("closedPerspective", Id("h"), p, q);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual s-finite complex L1 reverse-test class and the finite-alphabet class have equal extended infima for one specified convex closed-perspective cost.",
        H("The all-source bridge"), Blocks(
            Paragraph(Text("The output is any finite complex matrix algebra, including the empty index type. The two outputs need not be invertible, normalized or have the same trace. A preparation acts on the entire complex L1 space and is complex-linear, positive on the actual almost-everywhere nonnegative cone, and trace-preserving. Continuity is proved from these properties. The scalar generator is real valued and convex on the positive ray; both closed-perspective endpoints may be infinite.")),
            Node("source_atomization", SourceContext(Imp(FiniteCost, Atomization(Gamma(Input("p")), Gamma(Input("q")), Cost))),
                "For every specified finite source cost, an actual finite ReverseTest prepares the same two matrices and has exactly that one cost. Reweight by the nonnegative density p+q, represented using positive parts on a null exceptional set. The weighted source measure is finite even when the original source has infinite mass. The induced weighted map remains a positive complex-linear TP map on the entire new L1 space. No existence of a minimizing test is used. The interface asserts a finite alphabet without a numerical cardinality bound."),
            Node("source_class_infimum_eq", MatrixContext(Eq(Call("sInf", Call("allLoneCosts", Id("h"), Id("A"), Id("B"))),
                Call("sInf", Call("finiteCosts", Id("h"), Id("A"), Id("B"))))),
                "The two sets quantify all s-finite source spaces and all finite alphabets respectively, at the same fixed source universe. Finite tests embed through counting measure. Any all-source cost other than plus infinity is atomized exactly; plus infinity imposes no additional lower-bound obligation. Taking lower bounds proves equality in EReal, including unattained finite infima and empty feasible classes. This endpoint concerns one generator at a time, not simultaneous preservation of all generators or the full profile."),
            Node("finiteCosts_subset_allL1Costs", MatrixContext(Call("Subset",
                Call("finiteCosts", Id("h"), Id("A"), Id("B")),
                Call("allLoneCosts", Id("h"), Id("A"), Id("B")))),
                "Use counting measure on a universe lift of the finite labels. The map sends an arbitrary complex L1 input h to the finite sum of h(i) times its density state. This realizes the exact same matrices and extended perspective cost."),
            Node("allL1Costs_finite", MatrixContext(All("z", Call("EReal"), Imp(Call("Mem", Id("z"),
                Call("allLoneCosts", Id("h"), Id("A"), Id("B"))), Imp(Call("Ne", Id("z"), Call("Top")),
                Call("Mem", Id("z"), Call("finiteCosts", Id("h"), Id("A"), Id("B"))))))),
                "This applies the constructed atomization to each individual actual source test. It assumes no density representation or finite-moment supplier: both are proved from the original map."),
            Node("allL1Costs_of_positive_L1", PositiveInputContext(Call("Mem",
                Call("closedPerspectiveCost", Id("h"), Id("mu"), Call("RealPart", Id("p")), Call("RealPart", Id("q"))),
                Call("allLoneCosts", Id("h"), Gamma(Id("p")), Gamma(Id("q"))))),
                "The measurable representatives in L1ReverseTest do not restrict the actual source class. For any nonnegative elements p,q of the original complex L1 space, measurable integrable real representatives have the same complex L1 classes and the same cost. Almost-everywhere equality leaves both the finite affine integral and the nonnegative curvature integral unchanged."),
            Node("PositiveTracePreservingL1Map.norm_bound", BareMapContext(All("v", Call("ComplexLone", Id("alpha"), Id("mu")),
                Le(Call("Norm", Gamma(Id("v"))), Mul(D(4), Call("Norm", Id("v")))))),
                "Entrywise matrix norm is bounded by the real trace on positive matrices. Decompose a complex L1 input into the positive and negative parts of its real and imaginary coordinates. Trace preservation bounds each contribution by the original L1 norm. Thus positivity and TP imply boundedness, rather than continuity being a hidden extra source-class assumption."),
            Node("closedPerspectiveCost_withDensity", WeightedCost(),
                "Changing to a finite-valued nonnegative measurable density preserves the unnormalized perspective cost for arbitrary source measure and arbitrary real input functions. The real affine part uses the Bochner change-of-measure identity and the curvature part uses positive homogeneity under the extended nonnegative integral. Infinite axis values are retained."),
            Node("finite_cost_count", CountingCost(),
                "On a finite measurable alphabet, counting-measure integrals are the actual finite sums. The pointwise affine-plus-curvature identity, with its nonnegative extended remainder, proves the equality even when individual axis costs are infinite."),
            Node("finite_density_atomization", DensityAtomization(),
                "Apply the proved finite-moment theorem to two matrix moments and one real cost, restricting all selected points to the conull set where p,q are nonnegative and the perspective equals the finite real c. Multiply both scalar inputs at each selected point by its nonnegative cubature weight. Homogeneity proves exact preservation of this one cost. The zero measure uses the empty alphabet."),
            Node("finite_source_density", DensityContext(false),
                "Construct V(E) directly from the real L1 indicator action of the map. Positivity and the trace identity dominate its matrix norm by the source measure, proving countable additivity. Continuous coordinate projections give genuine complex measures. Apply the frozen positive_history_density theorem to this PositiveHistoryMeasure; Radon–Nikodym theory is reused, not rebuilt."),
            Node("finite_source_representation", DensityContext(true),
                "The density tau is measurable, integrable, positive semidefinite and trace one everywhere. The indicator identities extend to every integrable real L1 input by simple-function density and continuity of both the original action and the density-integral map. The chosen trace-one base handles the null exceptional set; zero source mass is allowed."),
            Paragraph(Text("For finite density moments, the norm bound on tau makes p tau and q tau Bochner integrable. A finite-cost affine-plus-curvature decomposition supplies an integrable real cost c and pointwise equality on a conull set. MeasurableFiniteMoments.finite_moments is applied to ((p tau,q tau),c), with all selected points in that conull set. Homogeneity of the closed perspective then gives exact equality of the finite sum. Infinite values on the null complement are never converted to real moments. When the output type is empty, trace preservation forces the nonnegative inputs to vanish almost everywhere; the empty finite test has exactly zero cost.")),
            Paragraph(Text("closedPerspectiveCost_withDensity uses the actual unnormalized affine integral plus nonnegative curvature remainder. It retains infinite axis costs and makes no normalization assumption. finite_cost_count identifies that same integral with the finite perspective sum. finitePreparationL1Map is the actual counting-measure preparation, L1ReverseTest records its two L1 inputs and exact output identities, finiteCosts ranges over Fin k, and allL1Costs ranges over every s-finite measurable source and actual preparation map.")),
            ProfileNode("L1ReverseTest.hockey", "The actual positive profile is the real Bochner integral of max(p-tq,0), for the actual integrable nonnegative inputs of the specified positive complex-linear TP L1 test.", false),
            ProfileNode("L1ReverseTest.negativeHockey", "The actual negative profile is the real Bochner integral of max(tq-p,0), over the same test and source measure.", false),
            ProfileNode("L1ReverseTest.hockey_integrable", "For every real threshold, integrability of p and q proves integrability of max(p-tq,0); the actual positive integral is finite.", true),
            ProfileNode("L1ReverseTest.negative_hockey_integrable", "For every real threshold, integrability of p and q proves integrability of max(tq-p,0); the actual negative integral is finite. This integrability is used in the direct construction.", true),
            ProfileNode("L1ReverseTest.input_masses", "TP on the actual complex L1 inputs gives integral p=Re Tr(A) and integral q=Re Tr(B), without trace normalization or a measure-class assumption.", true),
            ProfileNode("L1ReverseTest.negative_hockey_eq", "At every real threshold the negative integral equals the positive integral minus Re Tr(A) plus t Re Tr(B), by the scalar positive-part identity and the actual TP masses.", true),
            ProfileNode("L1ReverseTest.finite_hockey_realization", "For every actual L1 test on any measure and every specified t>0, there exists a finite ReverseTest preparing exactly A,B and realizing both actual hockey integrals at t. Set r=(p-tq)+, h=p-r=min(p,tq) almost everywhere and s=tq-h=(tq-p)+. Whole-domain complex L1 linearity and positivity make X=Gamma(h), A-X=Gamma(r), tB-X=Gamma(s) PSD, and TP gives Re Tr(X)=integral h. In nonempty output dimension use the existing independently indexed weighted-component supplier on three labels with components X,A-X,tB-X and weights (1,1,0),(1/t,0,1/t). In empty dimension TP forces p=q=0 almost everywhere and the genuinely empty alphabet realizes zero profiles. No coordinate or density state is used in the empty branch. This is HMT Proposition V.1, not new mathematics. The quantifiers are for every t>0 and every test there exists a finite test, not one finite test for all t.", true),
            ProfileNode("finiteL1ReverseTest", "Factor the counting-measure constructor already used by finiteCosts_subset_allL1Costs, on ULift of Fin k in the arbitrary source universe. Reuse finitePreparationL1Map on the entire complex L1 domain; the two inputs and exact preparations are unchanged.", false),
            ProfileNode("finiteL1ReverseTest_cost", "The factored counting embedding preserves the same extended closed-perspective cost, by finite_cost_count and the universe-lift sum equivalence. The existing finite-cost subset theorem consumes this helper.", true),
            ProfileNode("finiteL1ReverseTest_profiles", "The same factored counting embedding preserves both actual hockey integrals at every threshold, by integral_count and the universe-lift sum equivalence.", true),
            ProfileNode("positive_L1_profiles", "For any two original nonnegative complex L1 elements and any actual positive complex-linear TP map, the existing measurable representative construction gives an L1ReverseTest with the exact same prepared matrices and both literal real-part hockey integrals at every threshold. integral_congr_ae proves representative independence. No sigma-finite or s-finite premise is needed, and there is no silent measurable-density restriction.", true),
            ProfileNode("positive_L1_finite_hockey_realization", "The raw positive complex L1 inputs therefore admit the same fixed-positive-threshold finite realization of both literal hockey integrals, consuming positive_L1_profiles and the direct three-component theorem.", true),
            ProfileNode("sigmaFiniteHockeyProfiles", "Pairs of actual positive and negative hockey values of the same test at the specified threshold, quantified over every X in the arbitrary source universe, every measurable structure and sigma-finite measure, and every actual L1ReverseTest. Projecting the first or second coordinate gives exactly the respective original HMT value set.", false),
            ProfileNode("sFiniteHockeyProfiles", "The identical paired value set with every s-finite measure in place of sigma-finite; the source universe remains independent of the finite output universe.", false),
            ProfileNode("finiteHockeyProfiles", "Pairs of actual finite positive and negative profiles of the same ReverseTest, over all natural alphabet sizes.", false),
            ProfileNode("sigmaFiniteHockeyProfiles_eq", "At each positive threshold the original sigma-finite paired value set equals the finite paired value set. Forward inclusion uses direct per-test realization on the original measure; reverse inclusion uses actual universe-lifted finite counting preparation.", true),
            ProfileNode("sFiniteHockeyProfiles_eq", "At each positive threshold the full s-finite paired value set equals the same finite paired value set, by the same measure-independent realization and counting embedding.", true),
            ProfileNode("operationalL1Hockey", "The real infimum of the first projection of sigmaFiniteHockeyProfiles is precisely the original sigma-finite infimum of integral max(p-tq,0).", false),
            ProfileNode("operationalL1NegativeHockey", "The real infimum of the second projection of sigmaFiniteHockeyProfiles is precisely the original sigma-finite infimum of integral max(tq-p,0).", false),
            ProfileNode("sFiniteOperationalHockey", "The real infimum of the positive actual integral profile over every s-finite L1 source.", false),
            ProfileNode("sFiniteOperationalNegativeHockey", "The real infimum of the negative actual integral profile over every s-finite L1 source.", false),
            ProfileNode("operationalL1_eq_finite", "At every positive threshold both original sigma-finite operational infima and both s-finite infima equal the respective finite operational infima. The paired source-set equalities are proved before taking either infimum.", true),
            ProfileNode("operationalL1_hockey_eq", "For arbitrary finite PSD A,B and t>0, the actual positive operational infimum is Re Tr(A)-overlapValue(A,tB), and the actual negative infimum is t Re Tr(B)-overlapValue(A,tB), for both original sigma-finite and s-finite sources. The proof consumes operationalL1_eq_finite and the existing finite operational formulas. Those finite infima have nonempty attaining classes and are bounded below. Empty, singular and zero output pairs and arbitrary traces remain included. No closedPerspectiveCost is assumed to be a literal hinge integral.", true),
            ProfileNode("sigmaFiniteL1Costs", "The same actual closed-perspective cost class as allL1Costs, with the original sigma-finite measure quantifier and arbitrary independent source universe.", false),
            ProfileNode("sigma_finite_source_infimum_eq", "Finite counting sources are sigma-finite, and sigma-finite sources are s-finite. The original sigma-finite infimum is sandwiched between the already equal finite and s-finite extended infima. This faithful original-source identification is consumed by originalL1Value_eq_allL1Value.", true),
            Paragraph(Text("Matsumoto, A new quantum version of f-divergence, arXiv:1311.4722v4, p. 8, Lemma 4.1, proves one-cost finite-source compression with bound 2d^2+3. This interface asserts existence of a finite alphabet without a cardinality bound and makes no new compression claim. Its finite-moment implementation follows Bayer and Teichmann's proof of Tchakaloff's theorem through MeasurableFiniteMoments.finite_moments; the positive-history Radon-Nikodym theorem supplies the matrix density. MaximalHockeyStickAllL1Convex consumes source_class_infimum_eq to identify the actual all-L1 maximal convex value and transfer the finite equality criterion for the Hiai-Mosonyi-Tomamichel source question. The general-f bridge preserves one specified cost. The separate actual hockey bridge implements HMT Proposition V.1 by the direct min/three-component argument and preserves both orientations at one specified positive threshold; no finite test preserving all thresholds or every generator is asserted. MaximalHockeyStickAllL1Convex consumes the original sigma-finite and s-finite operational equalities in its integrated identity and final classifier."))
        )));

    private static Formula WeightedCost()
    {
        var weighted = Call("WithDensity", Id("mu"), Id("r"));
        var rp = Lambda("x", Mul(At(Id("r"), Id("x")), At(Id("p"), Id("x"))));
        var rq = Lambda("x", Mul(At(Id("r"), Id("x")), At(Id("q"), Id("x"))));
        var equation = Eq(Call("closedPerspectiveCost", Id("h"), weighted, Id("p"), Id("q")),
            Call("closedPerspectiveCost", Id("h"), Id("mu"), rp, rq));
        return ConvexContext(All("alpha", Call("Type"),
            Seq(OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")),
                All("r", Arrow(Id("alpha"), Call("NonnegativeReal")), Imp(Call("Measurable", Id("r")),
                All("p", Arrow(Id("alpha"), Real()), All("q", Arrow(Id("alpha"), Real()), equation))))))));
    }
    private static Formula CountingCost()
    {
        var equation = Eq(Call("closedPerspectiveCost", Id("h"), Call("Count", Id("beta")), Id("p"), Id("q")),
            Call("Sum", Lambda("i", PointCost(At(Id("p"), Id("i")), At(Id("q"), Id("i"))))));
        return ConvexContext(All("beta", Call("Type"),
            Seq(OpenBracket, Call("Fintype", Id("beta")), CloseBracket, Sp,
                OpenBracket, Call("MeasurableSpace", Id("beta")), CloseBracket, Sp,
                OpenBracket, Call("MeasurableSingletonClass", Id("beta")), CloseBracket, Sp,
                All("p", Arrow(Id("beta"), Real()), All("q", Arrow(Id("beta"), Real()),
                    Imp(Call("Nonnegative", Id("p")), Imp(Call("Nonnegative", Id("q")), equation)))))));
    }
    private static Formula DensityAtomization()
    {
        Formula Moment(string v) => Call("Integral", Lambda("x",
            Call("SMul", At(Id(v), Id("x")), At(Id("tau"), Id("x")))), Id("mu"));
        var cost = Call("Integral", Id("c"), Id("mu"));
        var pointwise = Call("AE", Id("mu"), Lambda("x", Eq(
            PointCost(At(Id("p"), Id("x")), At(Id("q"), Id("x"))), At(Id("c"), Id("x")))));
        var conclusion = Atomization(Moment("p"), Moment("q"), cost);
        var densities = All("p", Arrow(Id("alpha"), Real()), All("q", Arrow(Id("alpha"), Real()),
            All("c", Arrow(Id("alpha"), Real()), Imp(Call("Integrable", Id("p"), Id("mu")),
            Imp(Call("Integrable", Id("q"), Id("mu")), Imp(Call("Integrable", Id("c"), Id("mu")),
            Imp(Call("AENonnegative", Id("p"), Id("mu")), Imp(Call("AENonnegative", Id("q"), Id("mu")),
            Imp(pointwise, conclusion)))))))));
        return ScalarContext(All("alpha", Call("Type"),
            Seq(OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")), Imp(Call("IsFiniteMeasure", Id("mu")),
                All("tau", Arrow(Id("alpha"), Matrix), Imp(Call("Measurable", Id("tau")),
                Imp(All("x", Id("alpha"), And(Call("PosSemidef", At(Id("tau"), Id("x"))),
                    Eq(Call("Trace", At(Id("tau"), Id("x"))), D(1)))), densities))))))));
    }
    private static Formula ConvexContext(Formula body) =>
        All("f", Arrow(Real(), Real()), All("h", Convex, body));
    private static Formula Atomization(Formula a, Formula b, Formula cost) =>
        Exists("k", Call("Nat"), Exists("R", Call("ReverseTest", a, b, Id("k")),
            Eq(Call("Sum", Lambda("i", PointCost(Call("InputLeft", Id("R"), Id("i")),
                Call("InputRight", Id("R"), Id("i"))))), cost)));
    private static Formula SourceContext(Formula body) => MapContext(
        All("p", Arrow(Id("alpha"), Real()), All("q", Arrow(Id("alpha"), Real()),
            Imp(Call("Measurable", Id("p")), Imp(Call("Measurable", Id("q")),
            Imp(Call("Integrable", Id("p"), Id("mu")), Imp(Call("Integrable", Id("q"), Id("mu")),
            Imp(Call("AENonnegative", Id("p"), Id("mu")), Imp(Call("AENonnegative", Id("q"), Id("mu")), body)))))))));
    private static Formula PositiveInputContext(Formula body) => MapContext(
        All("p", Call("ComplexLone", Id("alpha"), Id("mu")),
        All("q", Call("ComplexLone", Id("alpha"), Id("mu")),
            Imp(Call("AENonnegative", Id("p"), Id("mu")), Imp(Call("AENonnegative", Id("q"), Id("mu")), body)))));
    private static Formula BareMapContext(Formula body) => All("n", Call("Type"),
        Seq(OpenBracket, Call("Fintype", Id("n")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", Id("n")), CloseBracket, Sp,
            All("alpha", Call("Type"), Seq(OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")),
                    All("Gamma", Call("PositiveTracePreservingLoneMap", Id("mu"), Id("n")), body))))));
    private static Formula MapContext(Formula body) => ScalarContext(
        All("alpha", Call("Type"), Seq(OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
        All("mu", Call("Measure", Id("alpha")), Imp(Call("SFinite", Id("mu")),
        All("Gamma", Call("PositiveTracePreservingLoneMap", Id("mu"), Id("n")), body))))));
    private static Formula MatrixContext(Formula body) => ScalarContext(
        All("A", Matrix, All("B", Matrix, body)));
    private static Formula ScalarContext(Formula body) => All("n", Call("Type"),
        Seq(OpenBracket, Call("Fintype", Id("n")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", Id("n")), CloseBracket, Sp,
            All("f", Arrow(Real(), Real()), All("h", Convex, body))));
    private static Formula DensityContext(bool allInputs)
    {
        var tau = Id("tau");
        var values = And(Call("Measurable", tau), And(Call("Integrable", tau, Id("mu")),
            All("x", Id("alpha"), And(Call("PosSemidef", At(tau, Id("x"))), Eq(Call("Trace", At(tau, Id("x"))), D(1))))));
        Formula identity = allInputs
            ? All("v", Call("RealLone", Id("alpha"), Id("mu")), Eq(At(Id("G"), Id("v")),
                Call("Integral", Lambda("x", Call("SMul", At(Id("v"), Id("x")), At(tau, Id("x")))), Id("mu"))))
            : All("E", Call("Set", Id("alpha")), Imp(Call("MeasurableSet", Id("E")),
                All("i", Id("n"), All("j", Id("n"), Eq(
                    Call("SetIntegral", Id("E"), Lambda("x", At(tau, Id("x"), Id("i"), Id("j"))), Id("mu")),
                    At(Id("G"), Call("LoneIndicator", Id("E"), Id("mu")), Id("i"), Id("j")))))));
        return All("n", Call("Type"), All("alpha", Call("Type"),
            Seq(OpenBracket, Call("Fintype", Id("n")), CloseBracket, Sp,
                OpenBracket, Call("DecidableEq", Id("n")), CloseBracket, Sp,
                OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")), Imp(Call("IsFiniteMeasure", Id("mu")),
                All("G", Call(allInputs ? "ContinuousRealLoneLinearMap" : "RealLoneLinearMap", Id("alpha"), Id("mu"), Matrix),
                Imp(Call("Positive", Id("G")), Imp(Call("TracePreserving", Id("G")),
                All("base", Matrix, Imp(Call("PosSemidef", Id("base")), Imp(Eq(Call("Trace", Id("base")), D(1)),
                    Exists("tau", Arrow(Id("alpha"), Matrix), And(values, identity)))))))))))));
    }
    private static DocumentBlock ProfileNode(string name, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("maximalhockeysticklone-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name.Replace("PositiveTracePreservingL1Map.", "").Replace("L1ReverseTest.", "")), H(name), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static DocumentBlock Node(string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("maximalhockeysticklone-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name.Replace("PositiveTracePreservingL1Map.", "").Replace("L1ReverseTest.", "")), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
}
