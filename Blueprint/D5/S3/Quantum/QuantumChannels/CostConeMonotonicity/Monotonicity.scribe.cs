using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.CostConeMonotonicity;

internal sealed class MonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.";
    private static readonly LibraryNoteRef Bptv =
        LibraryNoteRef.Create("D5/L/Convexity/bunthpitriktitkosvirosztek2025wasserstein");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Monotonicity of finite-spectrum quantum transport cost cones",
        H("Monotonicity of finite-spectrum quantum transport cost cones"),
        Blocks([
            .. SineSection.Content(),
            .. DecompositionSection.Content(),
            Paragraph(Text("The underlying space is any complete complex Hilbert space. No finite dimension or separability assumption is used. A finite-spectrum selfadjoint observable has bounded spectral support, so its spectral integral defines an everywhere defined bounded operator. Thus continuous linear endomorphisms retain the finite-spectrum observables in the source definition, even though its initial class also permits unbounded selfadjoint operators.")),
            Paragraph(Text("The cost is a finite sum of spectral projection tensors in the algebraic tensor product of the two operator algebras. The second factor is written before transposition. Applying the linear bijection from an operator to its transpose on the dual Hilbert space transports this expression to the source convention. The representation of the algebraic tensor product by operators on the Hilbert tensor product is injective: for linearly independent first factors, their matrix coefficient functionals separate their finite-dimensional span, and applying these functionals to a zero represented tensor forces every second factor to vanish. This explains the encoding; the Lean conclusion itself concerns the displayed algebraic tensor costs.")),
            Paragraph(Text("Finite lists encode finite indexed families, including repeated observables. A scalar shift of an observable preserves all spectral gaps and its cost. On a nonzero Hilbert space, finitely many distinct scalar shifts can therefore distinguish all repeated members without changing the sum; on the zero space every cost vanishes. This identifies the collection with the finite-set convention of equation (21). These comparisons explain the spectral-tensor encoding; they are not additional Lean bridge theorems. No approximate closure is added to the cost cone.")),
            Describe.Lean(DescribeId.Create("observable"), DeclarationHandle.Create(Prefix + "IsFiniteObservable"),
                H("Finite-spectrum selfadjoint observables"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Bptv),
                Blocks(Paragraph(Text("Selfadjoint continuous complex linear endomorphisms whose real spectrum is finite, as in equations (21) and (27)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("spectral-projection"), DeclarationHandle.Create(Prefix + "specProj"),
                H("A finite spectral projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Bptv),
                Blocks(Paragraph(Text("The real continuous functional calculus applied to the indicator of one spectral value. That indicator is continuous on a finite spectrum."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost-element"), DeclarationHandle.Create(Prefix + "costElem"),
                H("The order-p spectral cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Bptv),
                Blocks(Paragraph(Text("Sum over every pair of spectral values of the p-th real power of their absolute difference times the corresponding tensor of spectral projections, the finite-spectrum form of equation (22). The infinite-spectrum branch of this total function is unused in the cone."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cost-cone"), DeclarationHandle.Create(Prefix + "costCone"),
                H("Finite sums of observable costs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Bptv),
                Blocks(Paragraph(Text("The collection of finite sums of costs of finite-spectrum selfadjoint observables, corresponding to equation (27)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("finite-functional-calculus"), DeclarationHandle.Create(Prefix + "finiteObservable_cfc"),
                H("Functional calculus preserves the observable class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Bptv),
                Blocks(Paragraph(Text("Every real function on a finite spectrum gives another selfadjoint finite-spectrum observable."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("projection-fibers"), DeclarationHandle.Create(Prefix + "specProj_cfc"),
                H("Spectral projections after a change of labels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Bptv),
                Blocks(Paragraph(Text("The projection at v after functional calculus is the sum of the old projections whose labels map to v. The proof applies composition and finite summation in the continuous functional calculus."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cost-transport"), DeclarationHandle.Create(Prefix + "costElem_cfc"),
                H("Transport of the double spectral cost"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Bptv),
                Blocks(Paragraph(Text("Regrouping the two projection sums expresses the cost of f(A) using the original spectral projections and the distances between their new real labels."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("decomposition-lift"), DeclarationHandle.Create(Prefix + "costElem_of_decomposition"),
                H("Exact scalar decompositions lift to operator costs"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Bptv),
                Blocks(Paragraph(Text("An exact finite decomposition of every pair distance on the spectrum gives an exact finite sum of observable costs through functional calculus."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The finite-order cost-cone inclusion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Bptv),
                Blocks(Paragraph(Text("For real parameters 0<p and p at most q, every order-p cost belongs to the order-q cone. The equal-exponent case is immediate. For strict exponents, the positive sine integral represents each scalar distance power. Exact finite-dimensional conic cubature gives finitely many new scalar configurations; functional calculus lifts those configurations to new observables, and their costs sum exactly to the original cost. Replacing each member of a finite family proves the inclusion.")),
                    Paragraph(Text("This is the finite-parameter part of Conjecture 9, on Hilbert spaces without a separability restriction. The paper's Proposition 15 supplies the infinite endpoint. Its equations (49) and (50), and the stated concavity consequences for orders at most two, are consequences discussed by the source and are not separately formalized here. Proposition 13 gives reverse non-inclusion when the Hilbert space has dimension at least three, 0<p<pprime<infinity and pprime>1. For p=pprime=infinity the inclusion is reflexive."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bunth-pitrik-titkos-virosztek-2025-cost-cone-monotonicity"),
                    ResolutionKind.Proved))])));

private static class SineSection
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Convexity/bunthpitriktitkosvirosztek2025wasserstein");

    public static DocumentBlock[] Content()
    {
        var kernel = Reals(["p", "q", "u"],
            Eq(Call("sineKernel", V("p"), V("q"), V("u")), Kernel()));
        var moment = Reals(["p", "q"], Eq(Call("sineMoment", V("p"), V("q")),
            Call("IntegralOn", Call("Ioi", D(0)), Lambda("u", Kernel()))));
        var phase = Reals(["q"], Eq(Call("phaseMoment", V("q")),
            Call("IntervalIntegral", D(0), Mul(D(2), V("pi")),
                Lambda("theta", Pow(Abs(Call("cos", V("theta"))), V("q"))))));
        var measure = Eq(Call("sineParameterMeasure"), Call("ProductMeasure",
            Call("Restrict", V("volume"), Call("Ioi", D(0))),
            Call("Restrict", V("volume"), Call("Ioc", D(0), Mul(D(2), V("pi"))))));
        var sinx = Call("sin", Add(Mul(Call("fst", V("a")), V("x")), Call("snd", V("a"))));
        var siny = Call("sin", Add(Mul(Call("fst", V("a")), V("y")), Call("snd", V("a"))));
        var density = Pow(Call("fst", V("a")), Sub(Sub(D(0), D(1)), V("p")));
        var integrand = Reals(["p", "q", "x", "y"], All("a", Call("Prod", Real(), Real()),
            Eq(Integrand(), Mul(Pow(Abs(Sub(sinx, siny)), V("q")), density))));
        var momentPositive = Range(Lt(D(0), Call("sineMoment", V("p"), V("q"))));
        var phasePositive = Reals(["q"], Imp(Lt(D(0), V("q")),
            Lt(D(0), Call("phaseMoment", V("q")))));
        var integrable = Range(Reals(["x", "y"],
            Call("Integrable", Lambda("a", Integrand()), Call("sineParameterMeasure"))));
        var coefficient = Div(Mul(Mul(Pow(D(2), V("q")), Call("phaseMoment", V("q"))),
            Call("sineMoment", V("p"), V("q"))), Pow(D(2), V("p")));
        var identity = Range(Reals(["x", "y"], Eq(
            Call("Integral", Lambda("a", Integrand()), Call("sineParameterMeasure")),
            Mul(coefficient, Pow(Abs(Sub(V("x"), V("y"))), V("p"))))));
        return [
                Paragraph(Text("The positive mixture of q-power distances representing a p-power distance is classical metric-embedding background: the real-line snowflake admits an Lq representation, interpreted by its q-power integral also for q below one. It is used here as analytic background for the finite-exponent cost-cone inclusion. The distance mixture is over a positive dilation and a full phase period; all displayed integrals are real Bochner integrals. This is not a claim that the sine identity is a new result of Bunth, Pitrik, Titkos and Virosztek.")),
                Def("sineKernel", kernel,
                    "The kernel is the absolute sine to power q times u to power minus one minus p."),
                Def("sineMoment", moment,
                    "The sine moment integrates the kernel on the positive half-line."),
                Def("phaseMoment", phase,
                    "The phase moment integrates the absolute cosine power over one full period."),
                Def("sineParameterMeasure", measure,
                    "The dilation parameter lies in the positive half-line and the phase parameter lies in the half-open full period."),
                Def("sineDistanceIntegrand", integrand,
                    "The coordinate distance of the sine embedding is multiplied by the dilation density."),
                Thm("sineMoment_pos", momentPositive,
                    "For 0 < p < q, the sine moment is integrable and strictly positive. Near zero the kernel is bounded by u to power q minus p minus one; at infinity it is bounded by u to power minus p minus one. The interval from zero to pi lies in its nonzero support."),
                Thm("phaseMoment_pos", phasePositive,
                    "For q > 0, the phase integrand is continuous, nonnegative and positive at zero, so its full-period integral is positive."),
                Thm("integrable_sineDistance", integrable,
                    "The product-measure mixture is integrable. The full phase integral factors into the phase moment and a dilated sine kernel; Fubini's integrability criterion then applies."),
                Thm("integral_sineDistance", identity,
                    "The sine subtraction identity separates the difference and midpoint. Full-period translation invariance removes the midpoint, and a positive dilation gives the absolute difference to power p. The coefficient equals 2 to power q minus p times the two positive moments.")
        ];
    }

    private static DocumentBlock Def(string name, Formula formula, string prose) =>
        Node(name, formula, prose, DescribeRole.Definition);
    private static DocumentBlock Thm(string name, Formula formula, string prose) =>
        Node(name, formula, prose, DescribeRole.Theorem);
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("costcone-sine-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);
    private static Formula V(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Reals(string[] names, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; --i) body = All(names[i], Real(), body);
        return body;
    }
    private static Formula Range(Formula body) => Reals(["p", "q"],
        Imp(Lt(D(0), V("p")), Imp(Lt(V("p"), V("q")), body)));
    private static Formula Kernel() =>
        Mul(Pow(Abs(Call("sin", V("u"))), V("q")), Pow(V("u"), Sub(Sub(D(0), D(1)), V("p"))));
    private static Formula Integrand() => Call("sineDistanceIntegrand", V("p"), V("q"), V("x"), V("y"), V("a"));
    private static Formula Lambda(string name, Formula body) => Seq(V(name), Sp, Mapsto, Sp, body);
    private static Formula Real() => Seq(Mathbb, Grp(V("R")));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Abs(Formula a) => Call("abs", a);
}

private static class DecompositionSection
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/CostConeMonotonicity/Monotonicity.";
    private static readonly LibraryNoteRef Cubature = LibraryNoteRef.Create("D5/L/Convexity/bayerteichmann2006tchakaloff");
    private static readonly LibraryNoteRef Costs = LibraryNoteRef.Create("D5/L/Convexity/bunthpitriktitkosvirosztek2025wasserstein");

    public static DocumentBlock[] Content() => [
            Paragraph(Text("All powers are real powers of nonnegative real numbers. The configuration index is an arbitrary finite type, including an empty type. The sampling measure can have infinite mass. The finite-dimensional moment theorem applies after changing the measure by the norm density; no closedness of a distance cone or compactness of its normalized section is needed.")),
            Node("distanceVector", "Pair-distance vectors", All("I", Call("Type"),
                Quantify([("q", Real()), ("z", Arrow(Id("I"), Real())), ("i", Id("I")), ("j", Id("I"))],
                    Eq(Call("distanceVector", Id("q"), Id("z"), Pair(Id("i"), Id("j"))),
                        Pow(Abs(Sub(At(Id("z"), Id("i")), At(Id("z"), Id("j")))), Id("q"))))),
                "The vector has one real coordinate for every ordered pair. Diagonal coordinates and both orientations are retained.", DescribeRole.Definition, Costs),
            Node("finite_conic_moments", "Conic cubature on an arbitrary measure", ConicMoments(),
                "For an integrable strongly measurable map f into a finite-dimensional real normed space, use density norm(f) and normalize each nonzero f-value by its norm. The resulting measure is finite. Apply finite_moments on any prescribed conull set, then absorb the normalizing factors into the nonnegative coefficients. The empty witness covers zero moments and zero measure. The inherited finite-measure cubature theorem is attributed to Bayer and Teichmann; the norm-density extension is the composition proved here.", DescribeRole.Theorem, Cubature),
            Node("finite_distance_decomposition_of_integral", "Exact replacement of a distance integral", IntegralDecomposition(),
                "The vector integrand is r(a) times the q-distance vector of z(a). The real weight r is nonnegative almost everywhere, and its vector integral equals the target p-distance vector. Conic cubature selects points in that conull positivity set. Multiply each configuration by the q-th root of its total nonnegative coefficient. Homogeneity absorbs every coefficient, giving an unweighted finite sum of q-distance vectors.", DescribeRole.Theorem, Cubature),
            Node("finite_distance_decomposition", "Finite exact snowflake decomposition", FiniteDecomposition(),
                "For 0 < p < q, the phase-averaged sine representation supplies the integrable vector moment. Its positive normalization is incorporated into the scalar weight. The preceding exact-replacement theorem yields finitely many real configurations. No bound on their number is asserted, and no rationality or effective computation claim is made. This scalar decomposition is consumed by the finite-spectrum operator lift.", DescribeRole.Theorem, Costs)
    ];

    private static Formula ConicMoments()
    {
        var weightedValue = Lambda("i", Call("SMul", At(Id("w"), Id("i")), At(Id("f"), At(Id("a"), Id("i")))));
        var weights = All("i", Call("Fin", Id("k")), Le(D(0), At(Id("w"), Id("i"))));
        var labels = All("i", Call("Fin", Id("k")), Call("Mem", At(Id("a"), Id("i")), Id("s")));
        var equality = Eq(Call("Sum", weightedValue), Call("Integral", Id("f"), Id("mu")));
        var witness = Exists("k", Call("Nat"), Exists("w", Arrow(Call("Fin", Id("k")), Real()),
            Exists("a", Arrow(Call("Fin", Id("k")), Id("alpha")), And(Seq(Open, weights, Close), And(Seq(Open, labels, Close), equality)))));
        var good = Call("AE", Id("mu"), Lambda("a", Call("Mem", Id("a"), Id("s"))));
        var conclusion = Imp(Call("StronglyMeasurable", Id("f")), Imp(Call("Integrable", Id("f"), Id("mu")), Imp(good, witness)));
        return Quantify([("E", Call("Type")), ("alpha", Call("Type"))],
            Seq(Classes("E", "alpha"), Quantify([("mu", Call("Measure", Id("alpha"))),
                ("f", Arrow(Id("alpha"), Id("E"))), ("s", Call("Set", Id("alpha")))], conclusion)));
    }
    private static Formula IntegralDecomposition()
    {
        var integrand = Lambda("a", Call("SMul", At(Id("r"), Id("a")), Call("distanceVector", Id("q"), At(Id("z"), Id("a")))));
        var good = Call("AE", Id("mu"), Lambda("a", Le(D(0), At(Id("r"), Id("a")))));
        var moment = Eq(Call("Integral", integrand, Id("mu")), Call("distanceVector", Id("p"), Id("lambda")));
        return Context(Imp(Lt(D(0), Id("q")), Imp(good, Imp(Call("StronglyMeasurable", integrand),
            Imp(Call("Integrable", integrand, Id("mu")), Imp(moment, Witness()))))));
    }
    private static Formula FiniteDecomposition() =>
        All("I", Call("Type"), Seq(OpenBracket, Call("Fintype", Id("I")), CloseBracket,
            Quantify([("p", Real()), ("q", Real()), ("lambda", Arrow(Id("I"), Real()))],
                Imp(Lt(D(0), Id("p")), Imp(Lt(Id("p"), Id("q")), Witness())))));
    private static Formula Witness()
    {
        var left = Pow(Abs(Sub(At(Id("lambda"), Id("i")), At(Id("lambda"), Id("j")))), Id("p"));
        var right = Call("Sum", Lambda("l", Pow(Abs(Sub(At(Id("v"), Id("l"), Id("i")),
            At(Id("v"), Id("l"), Id("j")))), Id("q"))));
        return Exists("k", Call("Nat"), Exists("v", Arrow(Call("Fin", Id("k")), Arrow(Id("I"), Real())),
            Quantify([("i", Id("I")), ("j", Id("I"))], Eq(left, right))));
    }
    private static Formula Context(Formula body) => Quantify([("I", Call("Type")), ("alpha", Call("Type"))],
        Seq(OpenBracket, Call("Fintype", Id("I")), CloseBracket, Sp,
            OpenBracket, Call("MeasurableSpace", Id("alpha")), CloseBracket, Sp,
            Quantify([("mu", Call("Measure", Id("alpha"))), ("p", Real()), ("q", Real()),
                ("lambda", Arrow(Id("I"), Real())), ("z", Arrow(Id("alpha"), Arrow(Id("I"), Real()))),
                ("r", Arrow(Id("alpha"), Real()))], body)));
    private static Formula Quantify((string Name, Formula Type)[] binders, Formula body)
    {
        for (var i = binders.Length - 1; i >= 0; --i) body = All(binders[i].Name, binders[i].Type, body);
        return body;
    }
    private static Formula Classes(string e, string a) => Seq(
        OpenBracket, Call("NormedAddCommGroup", Id(e)), CloseBracket, Sp,
        OpenBracket, Call("NormedSpace", Real(), Id(e)), CloseBracket, Sp,
        OpenBracket, Call("FiniteDimensional", Real(), Id(e)), CloseBracket, Sp,
        OpenBracket, Call("MeasurableSpace", Id(a)), CloseBracket, Sp);
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, LibraryNoteRef source) => Describe.Lean(
            DescribeId.Create("bptv-finite-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(source), Blocks(Paragraph(Text(prose))), role);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Exists(string name, Formula type, Formula body) => Seq(FormulaDsl.Exists, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, b, Close);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
}

}
