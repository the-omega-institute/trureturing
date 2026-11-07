using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MomentMinors;

internal sealed class MansanarezPolySwanCumulantNonvanishingRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/MomentMinors/MansanarezPolySwanCumulantNonvanishingRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Estimation/mansanarez2024mmse");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite-support symmetric moment-determinate law refutes universal cumulant-coefficient nonvanishing.",
        H("The universal cumulant-coefficient condition fails"),
        Blocks(
            Node("AllMoments", "All moments are integrable", AllMomentsFormula(),
                "AllMoments μ states that every natural power of the identity function is integrable against μ.", true),
            Node("SMD", "Symmetric moment-determinate laws", SMDFormula(),
                "SMD μ states reflection invariance, integrability of every power, and uniqueness among probability measures with all moments and the same positive-order moments.", true),
            Node("cumulant", "Characteristic-function cumulants", CumulantFormula(),
                "For a real measure μ and natural n, cumulant uses the nth iterated derivative at zero of the principal complex logarithm of the real characteristic function, multiplied by (-I)^n and projected to the real part.", true),
            Node("shiftDerivative", "The shifted polynomial derivative", ShiftDerivativeFormula(),
                "The operator sums X(i+j) times the partial derivative in i over the finite variable support of a multivariate polynomial.", true),
            Node("sourceL", "The source L operator", SourceLFormula(),
                "sourceL is one half of the difference between two successive unit shifts and the shift by two.", true),
            Node("sourceH", "The source H operator", SourceHFormula(),
                "sourceH is the finite sum of the binomial inner derivative expression from Definition 3.8.", true),
            Node("sourceA", "The source A polynomial", SourceAFormula(),
                "sourceA is the negative finite binomial sum in Lemma 3.4.", true),
            Node("IsSourceSequence", "The recurrence-defined polynomial sequence", IsSourceSequenceFormula(),
                "The sequence starts with R₂ = 0 and R₃ = -2 X₂³ and satisfies the source recurrence for every n ≥ 3.", true),
            Node("linearCoefficient", "The linear monomial coefficient extractor", LinearCoefficientFormula(),
                "linearCoefficient keeps terms whose exponent at n is one and erases that exponent, summing over the polynomial support.", true),
            Node("coefficientForm", "The source coefficient aₙ", CoefficientFormFormula(),
                "coefficientForm applies linearCoefficient n to R at n+1.", true),
            Node("claim", "The universal nonvanishing assertion",
                ClaimFormula(),
                "Remark 3.31 states: “Let X be a symmetric random variable determined by its moments. Then X verifies \\eqref{Hypostar}.” The displayed Lean proposition additionally records the source recurrence sequence and quantifies the coefficient evaluation for every m ≥ 3. The source uses the local logarithmic characteristic-function cumulants and imposes no MGF, density or non-Gaussianity hypothesis.", true),
            ResultNode()),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, bool literature) =>
        Describe.Lean(DescribeId.Create("mps-cumulant-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))),
            name == "claim" ? DescribeRole.Definition : DescribeRole.Definition);

    private static DocumentBlock ResultNode() => Describe.Lean(
        DescribeId.Create("mps-cumulant-result"), DeclarationHandle.Create(Prefix + "result"),
        H("A finite-support counterexample"),
        StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
        AssessedProvenance.FromRepo(Source),
        Blocks(
            Paragraph(Text("For 0 < p < 1, the law with masses p/2, 1-p and p/2 at -1, 0 and 1 is a symmetric probability law with all moments and a direct three-point moment-determinacy argument. Its cumulants satisfy K₂ = p, K₄ = p - 3p², K₆ = p - 15p² + 30p³ and K₈ = p - 63p² + 420p³ - 630p⁴.")),
            Paragraph(Text("The quartic 56700p⁴ - 56700p³ + 18165p² - 1950p + 41 changes sign between 1/100 and 1/20. At its exact root, K₂, K₄ and K₆ are positive, K₈ is negative, and 21K₆² + 20K₄K₈ = 0. The source recurrence gives the evaluated coefficients a₆ = -140K₄², a₈ = -1008K₄K₆ and a₁₀ = -132(21K₆² + 20K₄K₈), so the m = 5 nonvanishing assertion fails while the earlier signs remain strict.")),
            Paragraph(Text("The source's Remark 1.5 prints -210 T₃T₆ for a₆; the defining recurrence gives -210 T₃T₅. Both mixed terms vanish for the symmetric witness, so the refutation uses the recurrence defined in Lemma 3.4."))),
        DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula MeasureR => Call("MeasureTheory.Measure", R);
    private static Formula Poly => Call("MvPolynomial", N, R);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args)
    {
        var parts = new List<Formula>();
        foreach (var word in name.Split('.'))
        {
            if (parts.Count > 0) parts.Add(Dot);
            parts.Add(F.Id(word));
        }
        var op = Seq(Operatorname, Grp([.. parts]));
        return args.Length == 0 ? op : new Formula.Apply(op, [.. args]);
    }
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(F.Id("fun"), Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, body));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Let(string name, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, V(name), Sp, Eq, Sp, value, Comma, Sp, body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Neg(Formula a) => new Formula.Negate(a);
    private static Formula Cast(Formula a, Formula type) => Parenthesized(Seq(a, Colon, Sp, type));
    private static Formula NatCast(Formula a, Formula type) => Cast(Call("Nat.cast", a), type);
    private static Formula RealConst(string value) => value switch
    {
        "1/2" => Cast(new Formula.Fraction(D(1), D(2)), R),
        "-1/2" => Cast(Neg(new Formula.Fraction(D(1), D(2))), R),
        "2" => Cast(D(2), R),
        _ => throw new ArgumentException("unsupported real constant", nameof(value))
    };
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), InMacro, Sp, set), Sp, Parenthesized(body));
    private static Formula X(Formula i) => Call("MvPolynomial.X", i);

    private static Formula AllMomentsFormula() => Disp(All("mu", MeasureR,
        All("n", N, Call("Integrable", Lambda("x", R, Pow(V("x"), V("n"))), V("mu")))));

    private static Formula SMDFormula()
    {
        Formula mu = V("mu"), nu = V("nu"), n = V("n");
        Formula moments = All("n", N, Imp(Le(D(1), n), Eqn(Call("moment", Call("id"), n, mu), Call("moment", Call("id"), n, nu))));
        Formula uniqueness = All("nu", MeasureR, Imp(Call("IsProbabilityMeasure", nu),
            Imp(Call("AllMoments", nu), Imp(moments, Eqn(mu, nu)))));
        return Disp(All("mu", MeasureR, And(Eqn(Call("Measure.map", Lambda("x", R, Neg(V("x"))), mu), mu),
            And(Call("AllMoments", mu), uniqueness))));
    }

    private static Formula CumulantFormula() => Disp(All("mu", MeasureR, All("n", N,
        Eqn(Call("cumulant", V("mu"), V("n")),
            Call("Complex.re", Mul(Pow(Neg(Call("Complex.I")), V("n")),
                Call("iteratedDeriv", V("n"), Lambda("t", R,
                    Call("Complex.log", Call("charFun", V("mu"), V("t")))), D(0))))))));

    private static Formula ShiftDerivativeFormula() => Disp(All("j", N, All("P", Poly,
        Eqn(Call("shiftDerivative", V("j"), V("P")),
            SumIn("i", Call("MvPolynomial.vars", V("P")),
                Mul(X(Add(V("i"), V("j"))), Call("MvPolynomial.pderiv", V("i"), V("P"))))))));

    private static Formula SourceLFormula() => Disp(All("P", Poly,
        Eqn(Call("sourceL", V("P")),
            Mul(Call("MvPolynomial.C", RealConst("1/2")),
                Sub(Call("shiftDerivative", D(1), Call("shiftDerivative", D(1), V("P"))),
                    Call("shiftDerivative", D(2), V("P")))))));

    private static Formula SourceHFormula()
    {
        Formula i = V("i"), l = V("l"), p = V("P");
        Formula inner = SumIn("l", Call("Finset.Ico", D(1), i),
            Mul(Mul(Call("MvPolynomial.C", NatCast(Call("Nat.choose", i, l), R)),
                    X(Add(D(1), l))),
                X(Sub(Add(D(1), i), l))));
        Formula term = Mul(Mul(Call("MvPolynomial.C", RealConst("-1/2")), inner),
            Call("MvPolynomial.pderiv", i, p));
        return Disp(All("P", Poly, Eqn(Call("sourceH", p),
            SumIn("i", Call("MvPolynomial.vars", p), term))));
    }

    private static Formula SourceAFormula() => Disp(All("n", N,
        Eqn(Call("sourceA", V("n")), Neg(SumIn("k", Call("Finset.Ico", D(1), V("n")),
            Mul(Mul(Mul(Call("MvPolynomial.C", NatCast(Call("Nat.choose", V("n"), V("k")), R)),
                    X(Add(D(1), V("k")))), X(Sub(Add(D(1), V("n")), V("k")))), X(V("n"))))))));

    private static Formula IsSourceSequenceFormula()
    {
        Formula Rv = V("R"), n = V("n");
        Formula recurrence = All("n", N, Imp(Le(D(3), n),
            Eqn(App(Rv, Add(n, D(1))), Add(Call("sourceA", n),
                Add(Call("sourceL", App(Rv, n)), Call("sourceH", App(Rv, n)))))));
        return Disp(All("R", Call("Function", N, Poly),
            And(Eqn(App(Rv, D(2)), Call("zero", Poly)),
                And(Eqn(App(Rv, D(3)), Neg(Mul(Mul(Call("MvPolynomial.C", RealConst("2")), X(D(2))), Pow(X(D(2)), D(2))))), recurrence))));
    }

    private static Formula LinearCoefficientFormula() => Disp(All("n", N, All("P", Poly,
        Eqn(Call("linearCoefficient", V("n"), V("P")),
            SumIn("d", Call("MvPolynomial.support", V("P")), Let("c", Call("MvPolynomial.coeff", V("P"), V("d")),
                Call("if", Eqn(App(V("d"), V("n")), D(1)),
                    Call("MvPolynomial.monomial", Call("Finsupp.erase", V("d"), V("n")), V("c")), D(0))))))));

    private static Formula CoefficientFormFormula() => Disp(All("R", Call("Function", N, Poly), All("n", N,
        Eqn(Call("coefficientForm", V("R"), V("n")),
            Call("linearCoefficient", V("n"), App(V("R"), Add(V("n"), D(1))))))));

    private static Formula ClaimFormula() => Disp(ClaimBody());

    private static Formula ClaimBody()
    {
        Formula Rv = V("R"), mu = V("mu"), m = V("m"), n = V("n");
        Formula source = Call("IsSourceSequence", Rv);
        Formula nonzero = Ne(Call("MvPolynomial.eval", Call("cumulant", mu),
            Call("coefficientForm", Rv, Mul(D(2), m))), D(0));
        Formula law = All("mu", MeasureR, Imp(Call("IsProbabilityMeasure", mu),
            Imp(Call("SMD", mu), All("m", N, Imp(Le(D(3), m), nonzero)))));
        return And(Some("R", Call("Function", N, Poly), source),
            All("R", Call("Function", N, Poly), Imp(source, law)));
    }
}
