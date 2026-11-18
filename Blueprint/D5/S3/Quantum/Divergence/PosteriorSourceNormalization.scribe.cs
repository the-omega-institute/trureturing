using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class PosteriorSourceNormalizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Divergence/PosteriorSourceNormalization.";
    private static Formula K => Call("Icc", D(0), D(1));
    private static Formula Nu => Call("posteriorMeasure", Id("mu"), Id("p"), Id("q"));
    private static Formula Theta => Call("theta", Id("p"), Id("q"));
    private static Formula J => Call("pullContinuous", Id("hpm"), Id("hqm"), Id("hp"), Id("hq"));
    private static Formula T => Lambda("t", Call("Subtype.val", Id("t")));
    private static Formula S => Lambda("t", Sub(D(1), Call("Subtype.val", Id("t"))));
    private static Formula Nonnegative(string name) => Call("AE", Id("mu"),
        Lambda("x", Le(D(0), At(Id(name), Id("x")))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual weighted posterior sources on the compact unit interval preserve the original complex L1 inputs and the exact extended closed-perspective cost.",
        H("Weighted posterior source normalization"), Blocks(
            Paragraph(Text("Let X be any measurable space in any source universe and mu any measure. The real inputs p and q are measurable, integrable and nonnegative almost everywhere; neither strict positivity nor total-mass normalization is assumed. Replace them pointwise by P=max(p,0) and Q=max(q,0), set r=P+Q, and define theta=P/r in K=[0,1], with theta=0 when r=0. The actual definitions use Real.toNNReal. The weighted measure is eta=mu.withDensity(r), and nu is its measurable pushforward by theta. Zero source measure and the zero pair remain included.")),
            Node("measurable_theta", Context(Call("Measurable", Theta), true, false, false),
                "Nonnegative finite representatives give a genuine K-valued measurable function, including exceptional null sets and zero fibers. The pointwise identities r theta=P and r(1-theta)=Q hold even when r=0."),
            Node("posteriorMeasure_eq_original", Context(Eq(Nu,
                Call("Map", Theta, Call("WithDensity", Id("mu"), Lambda("x",
                    Call("ENNReal.ofReal", Add(At(Id("p"), Id("x")), At(Id("q"), Id("x")))))))),
                false, false, true),
                "The nonnegative representatives agree with the literal original inputs almost everywhere. Therefore nu is exactly theta_*((p+q)mu), with the real density embedded by ENNReal.ofReal. This is an equality of measures, not an assumed change-of-source field."),
            Node("posteriorMeasure_finite_regular", Context(And(Call("IsFiniteMeasure", Nu),
                Call("Regular", Nu)), false, true, false),
                "Integrability of the positive parts proves that the integral of r is finite. The withDensity measure is finite and its pushforward is finite. The Borel measure on the compact metric interval is regular by Mathlib's regularity theorem. The theorem itself only needs integrability; nonnegativity of the original inputs is needed to identify the original weighted source."),
            Node("pullContinuous", Context(Call("HasType", J,
                Call("ContinuousComplexLinearMap", Call("ContinuousMap", K, Call("Complex")),
                    Call("ComplexLone", Id("X"), Id("mu")))), true, true, false),
                "Construct the actual continuous complex-linear map by composing ContinuousMap.toLp, Lp.compMeasurePreserving with theta, and the already established PositiveTracePreservingL1Map.weightMap. The latter is scalar despite its historical namespace. No state-valued Radon-Nikodym density, matrix representation or continuity of an original preparation is used.", false),
            Node("pullContinuous_coe", Context(All("g", Call("ContinuousMap", K, Call("Complex")),
                Call("EventuallyEq", Id("mu"), At(J, Id("g")), Lambda("x",
                    Call("SMul", Call("mass", Id("p"), Id("q"), Id("x")),
                        At(Id("g"), At(Theta, Id("x"))))))), true, true, false),
                "The a.e. value in the original complex L1 space is r(x)g(theta(x)). A weighted-measure exceptional set only transfers to mu away from r=0; the remaining fiber is handled by multiplication by zero. This supplies an actual original-domain input for every continuous complex g."),
            Node("pullContinuous_positive", Context(All("g", Call("ContinuousMap", K, Call("Complex")),
                Imp(All("t", K, Le(D(0), At(Id("g"), Id("t")))), Call("AE", Id("mu"),
                    Lambda("x", Le(D(0), At(J, Id("g"), Id("x"))))))), true, true, false),
                "Pointwise nonnegative continuous complex functions produce a.e. nonnegative original L1 inputs. Positivity uses the usual ComplexOrder cone."),
            Node("integral_pullContinuous", Context(All("g", Call("ContinuousMap", K, Call("Complex")),
                Eq(Call("Integral", Id("g"), Nu), Call("Integral", At(J, Id("g")), Id("mu")))),
                true, true, false),
                "The complex integral identity holds for every continuous g. It is the standard pushforward integral followed by the exact withDensity Bochner identity, and the L1 a.e. action above."),
            Node("pullContinuous_moments", Context(And(
                Eq(At(J, D(1)), Input(Lambda("x", Add(At(Id("p"), Id("x")),
                    At(Id("q"), Id("x")))), Call("Integrable.add", Id("hp"), Id("hq")))),
                And(Eq(At(J, Id("coordinate")), Input(Id("p"), Id("hp"))),
                    Eq(At(J, Sub(D(1), Id("coordinate"))), Input(Id("q"), Id("hq"))))),
                true, true, true),
                "coordinate(t) is the complex embedding of t.val. These are exact equalities to the L1 classes of the original p+q, p and q, respectively. Thus composition with any original algebraic preparation on the entire complex L1 space preserves both prepared moments. No continuity premise or smaller preparation domain is introduced."),
            Node("closedPerspectiveCost_posterior", Context(All("f", Arrow(Real(), Real()),
                All("hf", Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f")),
                    Eq(Call("closedPerspectiveCost", Id("hf"), Id("mu"), Id("p"), Id("q")),
                        Call("closedPerspectiveCost", Id("hf"), Nu, T, S)))), true, false, true),
                "Use the literal closedPerspectiveCost from CurvaturePerspectiveEndpoints and the existing closedPerspectiveCost_withDensity. The pointwise weighted identities restore the original inputs. Push forward the real affine-support integral and the extended nonnegative curvature integral separately. The equality needs neither integrability nor finiteness of the source or cost; those are used elsewhere to obtain a finite regular posterior and the L1 map. Infinite zero/infinity endpoints, zero masses and the origin convention are retained without signed infinity cancellation."),
            Paragraph(Text("This is the established weighted posterior construction, formalized as a consumed source-normalization supplier. The main reused ingredients are the project's exact homogeneous closed-perspective density-change theorem and scalar weightMap, and Mathlib's pushforward integration, Lp pullback, continuous-function Lp inclusion and finite Borel regularity APIs. It makes no novelty claim and does not establish arbitrary-von-Neumann reverse-test attainment, the chosen-predual identification, compactness of the normal-moment family, or the complete comparison of original source classes."))
        )));

    private static Formula Input(Formula function, Formula integrable) =>
        Call("Integrable.toLone", Call("Integrable.ofReal", integrable),
            Lambda("x", Call("Complex.ofReal", At(function, Id("x")))));

    private static Formula Context(Formula body, bool measurable, bool integrable, bool nonnegative)
    {
        if (nonnegative)
            body = All("hpn", Nonnegative("p"), All("hqn", Nonnegative("q"), body));
        if (integrable)
            body = All("hp", Call("Integrable", Id("p"), Id("mu")),
                All("hq", Call("Integrable", Id("q"), Id("mu")), body));
        if (measurable)
            body = All("hpm", Call("Measurable", Id("p")),
                All("hqm", Call("Measurable", Id("q")), body));
        return All("X", Call("Type"), All("mX", Call("MeasurableSpace", Id("X")),
            All("mu", Call("Measure", Id("X")), All("p", Arrow(Id("X"), Real()),
                All("q", Arrow(Id("X"), Real()), body)))));
    }

    private static DocumentBlock Node(string name, Formula statement, string prose, bool theorem = true) =>
        Describe.Lean(DescribeId.Create("posteriorsourcenormalization-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(statement)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);

    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name.Replace(".", "")))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, Par(body));
    private static Formula Arrow(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
}
