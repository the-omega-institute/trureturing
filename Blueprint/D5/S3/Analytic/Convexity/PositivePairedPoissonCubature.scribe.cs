using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Convexity;

internal sealed class PositivePairedPoissonCubatureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/Convexity/PositivePairedPoissonCubature.";
    private static readonly LibraryNoteRef FiniteCubatureSource =
        LibraryNoteRef.Create("D5/L/Convexity/bayerteichmann2006tchakaloff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constructed positive cosine density gives exact paired Poisson cubature for every finite initial segment of signed real data, using at most L+1 phases.",
        H("Positive paired Poisson finite cubature"), Blocks(
            Paragraph(Text("All coefficients, weights, angles and parameters are real. Natural indices begin at zero. SumFin(J,u) means the sum over j:Fin J; TsumNat(u) means the infinite sum over natural indices. NatCast is the natural-to-real coercion, IntervalIntegrable uses real Lebesgue measure, and Icc includes both endpoints. Function application in the formulas is ordinary point evaluation.")),
            Node("pairedMultiplier", MultiplierDefinition(),
                "The two geometric radii are 1/sigma and D*sigma. This definition makes the coefficient at zero equal to one. Positivity and summability require the hypotheses of the inverse theorem below.", false),
            Node("inverseCoeff", InverseDefinition(),
                "The inverse divides the supplied real coefficient by the paired multiplier. Nonvanishing of the multiplier is proved from nonnegative D and sigma>1; it is not an additional premise.", false),
            Node("weightedMass", WeightedMassDefinition(),
                "Only positive-index coefficients enter this absolute weighted mass. Summability and the displayed smallness bound control the oscillation of the inverse density.", false),
            Node("cosineDensity", DensityDefinition(),
                "Each positive cosine coefficient represents the two frequencies plus and minus n. The constant coefficient occurs once, and each positive-index coefficient occurs with factor two.", false),
            Node("haarMean", HaarDefinition(),
                "The normalized angular integral is (1/(2*pi)) times the interval integral from zero to 2*pi. It is defined for every real function with Mathlib's total integral convention.", false),
            Node("weighted_positive_paired_poisson_inverse", WeightedContext(InverseConclusions()),
                "For sigma>1, D>=0 and D*sigma^2<1 the multiplier is positive and bounded above by (1/sigma)^n. Its reciprocal is bounded by 2*sigma^n. Weighted absolute summability therefore gives absolute summability of the inverse coefficients. The smallness hypothesis yields 2*sum(abs(c(n+1)))<=4*weightedMass<=M/8. The synthesis is continuous, even and 2*pi-periodic, and is strictly greater than M/2 at every real angle. All thirteen conjunction clauses are retained, including both the pointwise coefficient identity and the synthesis identity.", true),
            Node("cosineDensity_haar_moments", HaarMoments(),
                "Absolute summability of arbitrary real coefficients, with no positivity premise, gives interval integrability, the exact mean c(0), and every positive cosine moment c(k). The proof uses integer cosine orthogonality and a uniform summable majorant to exchange the actual interval integral and series.", true),
            Node("weighted_positive_paired_poisson_finite_cubature", WeightedContext(Cubature()),
                "For every natural L, choose J first, then one pair of maps t and theta satisfying all moments 1<=k<=L simultaneously. There are no sign conditions on f(k) for k>0. The lower cardinality bound is one and the upper bound is L+1, including L=0, which forces J=1. Output weights are nonnegative and sum exactly to M/2; phases lie in the closed interval [0,2*pi]. The right side of each paired cosine moment is the signed value f(k)/2.", true),
            Paragraph(Text("For the finite-cubature foundation, the imported MeasurableFiniteMoments.integral_mem_convexHull places an integrable finite-dimensional probability barycenter in the actual convex hull. Its existing finite_moments_probability and finite_moments roots provide finite existence but assert no numerical cardinality bound. The classical provenance is Bayer and Teichmann, The proof of Tchakaloff's theorem, Corollary 2 and Remark 2; the existing Library note is the citation authority. The present root combines that foundation with the explicit geometric multiplier inverse and its actual Haar moments; no novelty claim is made.")),
            Paragraph(Text("Inside the proof put c(n)=inverseCoeff D sigma f n and rho=cosineDensity c. The inverse and scalar Haar theorem give rho>M/2 and haarMean(rho)=M. Normalize the actual measure with density ((1/(2*pi))/M)*rho relative to Lebesgue measure restricted to (0,2*pi]. Nonnegativity, continuity and the exact mean prove that its mass is one and prove the change-of-density identity.")),
            Paragraph(Text("Clamp each real input x to phase(x)=max(0,min(2*pi,x)); on (0,2*pi] this equals x. The map g(x)(i)=cos((i.val+1)*phase(x)) has values in Fin L to R and is bounded by one, so it is integrable, also for L=0. Apply the imported actual-hull theorem and Mathlib's eq_pos_convex_span_of_mem_convexHull. Affine independence bounds the number of points by finrank(vectorSpan(range z))+1<=L+1, and probability weight sum one forces at least one point. Lift the selected points to actual preimages and reindex by Fin J. Set theta(j)=phase(a(j)) and t(j)=(M/2)*p(j). The same selected maps then match each prescribed moment by the proved coefficient identity.")),
            Paragraph(Text("This is a finite-segment existence theorem over arbitrary signed real coefficient sequences satisfying the stated weighted bounds. It supplies no common nodes for all L, no full-spectrum equality for the finite measure, and no uniform choice across parameters. The strict positivity constructed internally is stronger than the nonnegativity requested in the output."))
        )));

    private static Formula MultiplierDefinition()
    {
        var n = Id("n");
        var rhs = Div(Add(Pow(Div(D(1), Id("sigma")), n), Pow(Mul(Id("D"), Id("sigma")), n)), D(2));
        var body = All("n", Nat(), Eqn(K(n), rhs));
        return All("D", Real(), All("sigma", Real(), body));
    }
    private static Formula InverseDefinition()
    {
        var n = Id("n");
        var body = All("n", Nat(), Eqn(C(n), Div(At(Id("f"), n), K(n))));
        body = All("f", Coeff(), body);
        return All("D", Real(), All("sigma", Real(), body));
    }
    private static Formula WeightedMassDefinition()
    {
        var tail = Mul(Abs(At(Id("f"), Succ(Id("n")))), Pow(Id("sigma"), Succ(Id("n"))));
        var body = Eqn(W(), Tsum("n", tail));
        return All("sigma", Real(), All("f", Coeff(), body));
    }
    private static Formula DensityDefinition()
    {
        var angle = Mul(Cast(Succ(Id("n"))), Id("theta"));
        var term = Mul(At(Id("c"), Succ(Id("n"))), Cos(angle));
        var rhs = Add(At(Id("c"), D(0)), Mul(D(2), Tsum("n", term)));
        var body = Eqn(Rho(Id("c"), Id("theta")), rhs);
        return All("c", Coeff(), All("theta", Real(), body));
    }
    private static Formula HaarDefinition()
    {
        var integral = Call("IntervalIntegral", Id("g"), D(0), TwoPi());
        var rhs = Mul(Div(D(1), TwoPi()), integral);
        return All("g", Arrow(Real(), Real()), Eqn(Call("haarMean", Id("g")), rhs));
    }
    private static Formula WeightedContext(Formula body)
    {
        var tail = Mul(Abs(At(Id("f"), Succ(Id("n")))), Pow(Id("sigma"), Succ(Id("n"))));
        body = Imp(Leqn(Mul(D(2), W()), Div(Id("M"), D(1, 6))), body);
        body = Imp(Call("Summable", Lambda("n", tail)), body);
        body = Imp(Eqn(At(Id("f"), D(0)), Id("M")), body);
        body = Imp(Ltqn(D(0), Id("M")), body);
        body = Imp(Ltqn(Mul(Id("D"), Pow(Id("sigma"), D(2))), D(1)), body);
        body = Imp(Leqn(D(0), Id("D")), body);
        body = Imp(Ltqn(D(1), Id("sigma")), body);
        body = All("f", Coeff(), body);
        body = All("M", Real(), body);
        body = All("sigma", Real(), body);
        return All("D", Real(), body);
    }

    private static Formula InverseConclusions()
    {
        var c = Call("inverseCoeff", Id("D"), Id("sigma"), Id("f"));
        var tailMass = Tsum("n", Abs(C(Succ(Id("n")))));
        return Conj(
            Call("Summable", Lambda("n", Abs(K(Id("n"))))),
            Eqn(K(D(0)), D(1)),
            All("n", Nat(), Conj(Ltqn(D(0), K(Id("n"))),
                Leqn(K(Id("n")), Pow(Div(D(1), Id("sigma")), Id("n"))))),
            Call("Summable", Lambda("n", Abs(C(Id("n"))))),
            Eqn(C(D(0)), Id("M")),
            Leqn(Mul(D(2), tailMass), Mul(D(4), W())),
            Leqn(Mul(D(4), W()), Div(Id("M"), D(8))),
            Call("Continuous", Call("cosineDensity", c)),
            All("theta", Real(), Eqn(Rho(c, new Formula.Negate(Id("theta"))), Rho(c, Id("theta")))),
            Call("Periodic", Call("cosineDensity", c), TwoPi()),
            All("theta", Real(), Ltqn(Div(Id("M"), D(2)), Rho(c, Id("theta")))),
            All("n", Nat(), Eqn(Mul(K(Id("n")), C(Id("n"))), At(Id("f"), Id("n")))),
            All("theta", Real(), Eqn(Rho(Lambda("n", Mul(K(Id("n")), C(Id("n")))), Id("theta")),
                Rho(Id("f"), Id("theta")))));
    }

    private static Formula HaarMoments()
    {
        var density = Call("cosineDensity", Id("c"));
        var moment = CosineMoment(Id("c"));
        var momentValue = Eqn(Call("haarMean", moment), At(Id("c"), Id("k")));
        var moments = All("k", Nat(), Imp(Ltqn(D(0), Id("k")),
            Conj(IntervalIntegrable(moment), momentValue)));
        var mean = Eqn(Call("haarMean", density), At(Id("c"), D(0)));
        var hypotheses = Call("Summable", Lambda("n", Abs(At(Id("c"), Id("n")))));
        return All("c", Coeff(), Imp(hypotheses, Conj(IntervalIntegrable(density), mean, moments)));
    }

    private static Formula Cubature()
    {
        var j = Id("j");
        var k = Id("k");
        var weights = All("j", Call("Fin", Id("J")), Leqn(D(0), At(Id("t"), j)));
        var mass = Eqn(SumFin(Id("J"), Id("t")), Div(Id("M"), D(2)));
        var phases = All("j", Call("Fin", Id("J")),
            Call("Mem", At(Id("theta"), j), Call("Icc", D(0), TwoPi())));
        var term = Mul(Mul(At(Id("t"), j), K(k)), Cos(Mul(Cast(k), At(Id("theta"), j))));
        var momentValue = Eqn(SumFin(Id("J"), Lambda("j", term)), Div(At(Id("f"), k), D(2)));
        var moments = All("k", Nat(), Imp(Leqn(D(1), k), Imp(Leqn(k, Id("L")), momentValue)));
        var body = Conj(weights, mass, phases, moments);
        body = Exists("theta", Arrow(Call("Fin", Id("J")), Real()), body);
        body = Exists("t", Arrow(Call("Fin", Id("J")), Real()), body);
        body = Conj(Leqn(D(1), Id("J")), Leqn(Id("J"), Succ(Id("L"))), body);
        return All("L", Nat(), Exists("J", Nat(), body));
    }

    private static Formula CosineMoment(Formula c) => Lambda("theta",
        Mul(Rho(c, Id("theta")), Cos(Mul(Cast(Id("k")), Id("theta")))));
    private static Formula IntervalIntegrable(Formula g) =>
        Call("IntervalIntegrable", g, Call("volume"), D(0), TwoPi());
    private static Formula K(Formula n) => Call("pairedMultiplier", Id("D"), Id("sigma"), n);
    private static Formula C(Formula n) => Call("inverseCoeff", Id("D"), Id("sigma"), Id("f"), n);
    private static Formula W() => Call("weightedMass", Id("sigma"), Id("f"));
    private static Formula Rho(Formula c, Formula theta) => Call("cosineDensity", c, theta);
    private static Formula TwoPi() => Mul(D(2), Pi);
    private static Formula Coeff() => Arrow(Nat(), Real());
    private static Formula Nat() => Seq(Mathbb, Grp(Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(Id("R")));
    private static Formula Cast(Formula n) => Call("NatCast", n);
    private static Formula Succ(Formula n) => Add(n, D(1));
    private static Formula Cos(Formula x) => Call("cos", x);
    private static Formula Abs(Formula x) => new Formula.Absolute(x);
    private static Formula Pow(Formula x, Formula n) => new Formula.Power(Par(x), n);
    private static Formula Div(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Tsum(string name, Formula body) => Call("TsumNat", Lambda(name, body));
    private static Formula SumFin(Formula count, Formula body) => Call("SumFin", count, body);
    private static Formula Conj(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(Par(clauses[i]), FormulaLogicOperator.And, Par(result));
        return result;
    }
    private static DocumentBlock Node(string name, Formula formula, string prose, bool theorem) =>
        Describe.Lean(DescribeId.Create("positivepairedpoissoncubature-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(name), StatementSource.FromAuthor(Disp(formula)),
            theorem && name == "weighted_positive_paired_poisson_finite_cubature"
                ? AssessedProvenance.FromRepo(FiniteCubatureSource) : AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), theorem ? DescribeRole.Theorem : DescribeRole.Definition);
    private static Formula Id(string name) => FormulaDsl.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(Id(name))), [.. args]);
    private static Formula At(Formula value, params Formula[] args) => new Formula.Apply(value, [.. args]);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Exists(string name, Formula type, Formula body) =>
        Seq(FormulaDsl.Exists, Sp, Id(name), Sp, Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Lambda(string name, Formula body) => Seq(Id(name), Sp, Mapsto, Sp, Par(body));
    private static Formula Arrow(Formula a, Formula b) => Par(Seq(a, Sp, To, Sp, b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, Par(b));
    private static Formula Leqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ltqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Add, Par(b));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(Par(a), FormulaBinaryOperator.Multiply, Par(b));
}
