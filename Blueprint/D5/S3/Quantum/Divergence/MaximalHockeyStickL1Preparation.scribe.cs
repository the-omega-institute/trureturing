using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class MaximalHockeyStickL1PreparationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/MaximalHockeyStickL1Preparation.";
    private static Formula Matrix => Call("Matrix", Id("n"), Id("n"), Call("Complex"));
    private static Formula Gamma(Formula v) => At(Id("Gamma"), v);
    private static Formula Convex => Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f"));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive trace-preserving complex L1 maps, finite-source density representation and change of density.",
        H("Preparation on the entire complex L1 space"), Blocks(
            Paragraph(Text("The source measure and measurable space are arbitrary, and the output is any finite complex matrix algebra, including empty dimension. Positivity and trace preservation hold on the entire complex L1 domain; continuity is derived. Finite-source density representation uses a supplied trace-one base only to repair a null exceptional set. No optimizer or invertibility hypothesis is introduced.")),
            Node("PositiveTracePreservingL1Map.norm_bound", BareMapContext(All("v", Call("ComplexLone", Id("alpha"), Id("mu")),
                Le(Call("Norm", Gamma(Id("v"))), Mul(D(4), Call("Norm", Id("v")))))),
                "Entrywise matrix norm is bounded by the real trace on positive matrices. Decompose a complex L1 input into the positive and negative parts of its real and imaginary coordinates. Trace preservation bounds each contribution by the original L1 norm. Thus positivity and TP imply boundedness, rather than continuity being a hidden extra source-class assumption."),
            Node("closedPerspectiveCost_withDensity", WeightedCost(),
                "Changing to a finite-valued nonnegative measurable density preserves the unnormalized perspective cost for arbitrary source measure and arbitrary real input functions. The real affine part uses the Bochner change-of-measure identity and the curvature part uses positive homogeneity under the extended nonnegative integral. Infinite axis values are retained."),
            Node("finite_source_density", DensityContext(false),
                "Construct V(E) directly from the real L1 indicator action of the map. Positivity and the trace identity dominate its matrix norm by the source measure, proving countable additivity. Continuous coordinate projections give genuine complex measures. Apply the frozen positive_history_density theorem to this PositiveHistoryMeasure; Radon–Nikodym theory is reused, not rebuilt."),
            Node("finite_source_representation", DensityContext(true),
                "The density tau is measurable, integrable, positive semidefinite and trace one everywhere. The indicator identities extend to every integrable real L1 input by simple-function density and continuity of both the original action and the density-integral map. The chosen trace-one base handles the null exceptional set; zero source mass is allowed."),
            Paragraph(Text("PositiveTracePreservingL1Map.weightMap and weightMap_coe implement the actual change of density and its almost-everywhere action. psd_norm_le_trace and closedPerspective_homogeneous are used both here and in MaximalHockeyStickL1ReverseTest's finite-moment atomization. That consumer retains the original sigma-finite and s-finite source equivalences. The coordinate density theorem reuses MeasurableInstrumentHistory.positive_history_density; the homogeneity identity retains infinite convex endpoint costs."))
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
    private static Formula ConvexContext(Formula body) =>
        All("f", Arrow(Real(), Real()), All("h", Convex, body));
    private static Formula BareMapContext(Formula body) => All("n", Call("Type"),
        Seq(OpenBracket, Call("Fintype", Id("n")), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", Id("n")), CloseBracket, Sp,
            All("alpha", Call("Type"), Seq(OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
                All("mu", Call("Measure", Id("alpha")),
                    All("Gamma", Call("PositiveTracePreservingLoneMap", Id("mu"), Id("n")), body))))));
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
    private static DocumentBlock Node(string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("maximalhockeysticklonepreparation-" + name.Replace("_", "-").Replace(".", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name.Replace("PositiveTracePreservingL1Map.", "")), H(name), StatementSource.FromAuthor(Disp(formula)),
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
