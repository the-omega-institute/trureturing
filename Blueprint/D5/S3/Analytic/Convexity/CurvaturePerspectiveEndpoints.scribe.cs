using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class CurvaturePerspectiveEndpointsDocument : IScribeDocumentDefinition
{
    // A declaration handle selects its physical source module, then its name suffix.
    // The Lean namespace is CurvatureHingeRepresentation.
    private const string Prefix = "D5/S3/Analytic/Convexity/CurvaturePerspectiveEndpoints.";
    private static Formula Fn => Arrow(Real(), Real());
    private static Formula Convex => Call("ConvexOn", Real(), Call("Ioi", D(0)), Id("f"));
    private static Formula Mu => Call("curvature", Id("h"));
    private static Formula Slope => Call("rightDeriv", Id("f"), D(1));
    private static Formula Zero => Call("zeroEndpoint", Id("h"));
    private static Formula Infinity => Call("infinityEndpoint", Id("h"));
    private static Formula Remainder => Call("curvatureRemainder", Id("h"), Id("u"), Id("v"));
    private static Formula Perspective => Call("closedPerspective", Id("h"), Id("u"), Id("v"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extended convex endpoints and the closed perspective are obtained from actual positive Stieltjes curvature, including infinite costs.",
        H("Extended endpoints, axes and cost integration"), Blocks(
            Paragraph(Text("Assume only that f is real valued and convex on the strictly positive ray. The curvature measure is the actual right-derivative Stieltjes measure constructed in CurvatureHingeRepresentation. The endpoint declarations retain that Lean namespace but are owned by the CurvaturePerspectiveEndpoints source module; each Describe handle selects that module and the declaration suffix. Integrals denoted LIntegral are extended nonnegative Lebesgue integrals. Finite real terms and nonnegative extended terms are embedded in EReal. No subtraction of infinite values occurs. The base one in each curvature domain is the positive subtype element one.")),
            Node("zeroEndpoint", Eqn(Zero, Add(Sub(Call("f", D(1)), Slope),
                LI(Call("Iic", D(1)), Call("ENNReal.ofReal", Id("t")), Mu))),
                "The zero endpoint is a finite affine constant plus the possibly infinite first curvature moment over (0,1]. It is never minus infinity.", false),
            Node("infinityEndpoint", Eqn(Infinity, Add(Slope, At(Mu, Call("Ioi", D(1))))),
                "The asymptotic slope is a finite slope plus the possibly infinite total curvature on (1,infinity). Total curvature is not assumed finite.", false),
            Node("tendsto_zeroEndpoint", Call("Tendsto",
                Lambda("s", Call("EReal.ofReal", Call("f", Id("s")))), Call("atBotPositive"), Call("nhds", Zero)),
                "As the positive scalar decreases to zero, the lower curvature kernels increase to t. Monotone convergence first proves the limit along a cofinal sequence and monotonicity then proves the full filter limit. The finite affine term converges independently.", true),
            Node("tendsto_infinityEndpoint", Call("Tendsto",
                Lambda("s", Call("EReal.ofReal", Call("div", Call("f", Id("s")), Id("s")))),
                Call("atTopPositive"), Call("nhds", Infinity)),
                "As s tends to infinity, the normalized upper curvature kernels (1-t/s)+ increase to one. Monotone convergence permits infinite tail mass and proves the actual asymptotic slope.", true),
            Node("curvatureRemainder", All("u", Real(), All("v", Real(), Eqn(Remainder,
                Add(LI(Call("Iic", D(1)), Call("ENNReal.ofReal", Sub(Mul(Id("t"), Id("v")), Id("u"))), Mu),
                    LI(Call("Ioi", D(1)), Call("ENNReal.ofReal", Sub(Id("u"), Mul(Id("t"), Id("v")))), Mu))))),
                "The remainder is nonnegative and may be infinite on the axes. The atom at one is in the negative branch, whose domain is (0,1].", false),
            Node("closedPerspective", All("u", Real(), All("v", Real(), Eqn(Perspective,
                Call("ite", Eqn(Id("v"), D(0)), Mul(Id("u"), Infinity),
                    Call("ite", Eqn(Id("u"), D(0)), Mul(Id("v"), Zero),
                        Mul(Id("v"), Call("f", Call("div", Id("u"), Id("v"))))))))),
                "For positive u and v this is v f(u/v). On either nonzero axis it is the corresponding positive scalar times the proved convex endpoint limit. At the origin it is zero, including when the endpoint is infinite.", false),
            Node("closedPerspective_eq_affine_add_curvature", All("u", Real(), All("v", Real(),
                Imp(Leqn(D(0), Id("u")), Imp(Leqn(D(0), Id("v")), Eqn(Perspective,
                    Add(Add(Mul(Call("f", D(1)), Id("v")), Mul(Slope, Sub(Id("u"), Id("v")))), Remainder)))))),
                "This proves the scalar identity on the entire nonnegative quadrant. The interior follows from the finite scalar representation and integrability of the compactly supported hinges. On the axes, scaling the explicit endpoint curvature integrals gives the same identity; no infinite difference is formed.", true),
            Node("closedPerspective_origin", Eqn(Call("closedPerspective", Id("h"), D(0), D(0)), D(0)),
                "The corner contributes zero even when one or both convex endpoints are infinite.", true),
            Node("integral_curvatureRemainder", Tonelli(),
                "For any measurable space, s-finite measure nu and measurable real functions p,q, the integral of curvatureRemainder h (p x) (q x) equals the sum of the curvature integrals of the integrated negative and positive hockey-stick kernels. Both sides are extended nonnegative integrals. Joint measurability is proved from p and q, then Tonelli is applied to each branch. No cost finiteness assumption is used.", true),
            Node("closedPerspectiveCost", CostDefinition(),
                "For nonnegative densities, the pointwise closed-perspective representation proves that this is the actual perspective integral with finite affine subtraction. It is defined as the real integral of the affine support plus the extended nonnegative integral of curvatureRemainder. The latter may be infinite.", false),
            Node("closedPerspectiveCost_eq_mass", MassCost(),
                "For arbitrary measurable integrable densities, the affine term is f(1) times the q mass plus the right derivative at one times the difference of the p and q masses. Both nonnegative curvature integrals remain extended valued. There is no normalization of the inputs and no infinite subtraction.", true),
            Node("closedPerspectiveCost_eq", NormalizedCost(),
                "On any s-finite measure space with measurable integrable real densities p and q of integral one, the cost equals f(1) plus the two integrated hockey-stick remainders. For nonnegative densities this is the actual closed-perspective cost. Integrability justifies the finite affine integral, whose derivative term cancels; Tonelli justifies the two nonnegative curvature integrals even when the cost is infinite.", true)
        )));

    private static Formula CostDefinition()
    {
        var affine = Add(Mul(Call("f", D(1)), Call("q", Id("x"))),
            Mul(Slope, Sub(Call("p", Id("x")), Call("q", Id("x")))));
        var remainder = Call("curvatureRemainder", Id("h"), Call("p", Id("x")), Call("q", Id("x")));
        return All("alpha", Call("Type"), All("m", Call("MeasurableSpace", Id("alpha")),
            All("nu", Call("Measure", Id("alpha")), All("p", Arrow(Id("alpha"), Real()),
            All("q", Arrow(Id("alpha"), Real()), Eqn(Call("closedPerspectiveCost", Id("h"), Id("nu"), Id("p"), Id("q")),
                Add(Call("Integral", Lambda("x", affine), Id("nu")),
                    Call("LIntegral", Lambda("x", remainder), Id("nu")))))))));
    }

    private static Formula MassCost()
    {
        var negative = Call("ENNReal.ofReal", Sub(Mul(Id("t"), Call("q", Id("x"))), Call("p", Id("x"))));
        var positive = Call("ENNReal.ofReal", Sub(Call("p", Id("x")), Mul(Id("t"), Call("q", Id("x")))));
        var pMass = Call("Integral", Lambda("x", Call("p", Id("x"))), Id("nu"));
        var qMass = Call("Integral", Lambda("x", Call("q", Id("x"))), Id("nu"));
        var affine = Add(Mul(Call("f", D(1)), qMass), Mul(Slope, Sub(pMass, qMass)));
        var rhs = Add(affine, Add(
            LI(Call("Iic", D(1)), Call("LIntegral", Lambda("x", negative), Id("nu")), Mu),
            LI(Call("Ioi", D(1)), Call("LIntegral", Lambda("x", positive), Id("nu")), Mu)));
        var equality = Eqn(Call("closedPerspectiveCost", Id("h"), Id("nu"), Id("p"), Id("q")), rhs);
        var hypotheses = Imp(Call("SFinite", Id("nu")), Imp(Call("Measurable", Id("p")),
            Imp(Call("Measurable", Id("q")), Imp(Call("Integrable", Id("p"), Id("nu")),
            Imp(Call("Integrable", Id("q"), Id("nu")), equality)))));
        return All("alpha", Call("Type"), All("m", Call("MeasurableSpace", Id("alpha")),
            All("nu", Call("Measure", Id("alpha")), All("p", Arrow(Id("alpha"), Real()),
            All("q", Arrow(Id("alpha"), Real()), hypotheses)))));
    }

    private static Formula NormalizedCost()
    {
        var negative = Call("ENNReal.ofReal", Sub(Mul(Id("t"), Call("q", Id("x"))), Call("p", Id("x"))));
        var positive = Call("ENNReal.ofReal", Sub(Call("p", Id("x")), Mul(Id("t"), Call("q", Id("x")))));
        var rhs = Add(Call("f", D(1)), Add(
            LI(Call("Iic", D(1)), Call("LIntegral", Lambda("x", negative), Id("nu")), Mu),
            LI(Call("Ioi", D(1)), Call("LIntegral", Lambda("x", positive), Id("nu")), Mu)));
        var equality = Eqn(Call("closedPerspectiveCost", Id("h"), Id("nu"), Id("p"), Id("q")), rhs);
        var hypotheses = Imp(Call("SFinite", Id("nu")), Imp(Call("Measurable", Id("p")),
            Imp(Call("Measurable", Id("q")), Imp(Call("Integrable", Id("p"), Id("nu")),
            Imp(Call("Integrable", Id("q"), Id("nu")),
            Imp(Eqn(Call("Integral", Lambda("x", Call("p", Id("x"))), Id("nu")), D(1)),
            Imp(Eqn(Call("Integral", Lambda("x", Call("q", Id("x"))), Id("nu")), D(1)), equality)))))));
        return All("alpha", Call("Type"), All("m", Call("MeasurableSpace", Id("alpha")),
            All("nu", Call("Measure", Id("alpha")), All("p", Arrow(Id("alpha"), Real()),
            All("q", Arrow(Id("alpha"), Real()), hypotheses)))));
    }

    private static Formula Tonelli()
    {
        var negative = Call("ENNReal.ofReal", Sub(Mul(Id("t"), Call("q", Id("x"))), Call("p", Id("x"))));
        var positive = Call("ENNReal.ofReal", Sub(Call("p", Id("x")), Mul(Id("t"), Call("q", Id("x")))));
        var lhs = Call("LIntegral", Lambda("x", Call("curvatureRemainder", Id("h"), Call("p", Id("x")), Call("q", Id("x")))), Id("nu"));
        var rhs = Add(LI(Call("Iic", D(1)), Call("LIntegral", Lambda("x", negative), Id("nu")), Mu),
            LI(Call("Ioi", D(1)), Call("LIntegral", Lambda("x", positive), Id("nu")), Mu));
        return All("alpha", Call("Type"), All("m", Call("MeasurableSpace", Id("alpha")),
            All("nu", Call("Measure", Id("alpha")), All("p", Arrow(Id("alpha"), Real()),
            All("q", Arrow(Id("alpha"), Real()), Imp(Call("SFinite", Id("nu")),
            Imp(Call("Measurable", Id("p")), Imp(Call("Measurable", Id("q")), Eqn(lhs, rhs)))))))));
    }

    private static DocumentBlock Node(string name, Formula formula, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("curvatureperspectiveendpoints-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(All("f", Fn, All("h", Convex, formula)))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))),
            theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name.Replace(".", "")))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, Par(body));
    private static Formula Arrow(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Par(b));
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Subtract, Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula LI(Formula domain, Formula body, Formula measure) => Call("LIntegral", domain, Lambda("t", body), measure);
}
