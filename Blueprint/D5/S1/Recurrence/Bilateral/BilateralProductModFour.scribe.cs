using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class BilateralProductModFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/BilateralProductModFour.";
    private static readonly LibraryNoteRef SourceTwo =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a381362");
    private static readonly LibraryNoteRef SourceThree =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a381363");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's bilateral product family has every positive coefficient equal to two modulo four.",
        H("The Bilateral Product Family of A381362 and A381363"),
        Blocks(
            Supplier("positiveTerm", "The positive-index integral term",
                "The term at a positive index k contains X to the power k and the two polynomial factors in the bilateral product.", DescribeRole.Definition),
            Supplier("negativeTerm", "The negative-index integral term",
                "Factoring the negative Laurent powers produces X to the power c*k squared and integral unit inverses.", DescribeRole.Definition),
            Supplier("Agree", "Agreement below a degree",
                "Two integer power series agree below d exactly when their coefficients at every n less than d coincide.", DescribeRole.Definition),
            Supplier("agree_iff", "Agreement is divisibility by a power of X",
                "Agreement below d is equivalent to divisibility of the difference by X to the power d.", DescribeRole.Theorem),
            Supplier("agree_refl", "A series agrees with itself",
                "Every integer power series agrees with itself below every natural degree.", DescribeRole.Theorem),
            Supplier("agree_add", "Sums preserve agreement",
                "Adding two pairs of series that agree below d preserves agreement below d.", DescribeRole.Theorem),
            Supplier("agree_mul", "Products preserve agreement",
                "Multiplying two pairs of series that agree below d preserves agreement below d.", DescribeRole.Theorem),
            Supplier("agree_pow", "Natural powers preserve agreement",
                "Equal coefficients below d remain equal after taking the same natural power.", DescribeRole.Theorem),
            Supplier("agree_inverse", "Normalized unit inverses preserve agreement",
                "For two series of constant coefficient one, agreement below d passes to their integral unit inverses.", DescribeRole.Theorem),
            Supplier("agree_shift", "A positive shift improves agreement",
                "Multiplication by X to any positive power improves agreement from d to d+1.", DescribeRole.Theorem),
            Supplier("geometric", "The integral geometric series",
                "This is invOfUnit(1+X,1), the normalized integral inverse of 1+X.", DescribeRole.Definition),
            Supplier("geometric_spec", "The geometric inverse identity",
                "Multiplying the geometric series by 1+X gives one.", DescribeRole.Theorem),
            Supplier("geometric_coeff", "The alternating geometric coefficients",
                "The coefficient at every natural n is (-1) to the power n.", DescribeRole.Theorem),
            Supplier("step", "The integral fixed-point operator",
                "For every natural c and integer series A, the step is 2*geometric-1+2*(1+A)*nonzeroSum(c,A).", DescribeRole.Definition),
            Supplier("approximation", "The successive integral approximations",
                "The initial approximation is one; each successor is obtained by applying step at the same parameter c.", DescribeRole.Definition),
            Supplier("equation_iff", "The polynomial equation is the fixed-point equation",
                "For every natural c and integer series A, multiplying out the polynomial equation is equivalent to A=step(c,A).", DescribeRole.Theorem),
            Supplier("embed", "Embedding integer series into rational Laurent series",
                "Map each integer coefficient to the rationals and then apply HahnSeries.ofPowerSeries with integer exponents.", DescribeRole.Definition),
            Supplier("embed_coeff", "The embedding preserves nonnegative coefficients",
                "At each natural degree N, the Laurent coefficient is the rational image of the original integer coefficient.", DescribeRole.Theorem),
            Supplier("embed_injective", "The Laurent embedding is injective",
                "Equality of the embedded Laurent series implies equality of the original integer power series.", DescribeRole.Theorem),
            Supplier("embed_inverse", "The embedding preserves a normalized inverse",
                "For an integer series with constant coefficient one, the embedding sends invOfUnit(A,1) to the inverse of embed(A).", DescribeRole.Theorem),
            Supplier("negative_factorization", "Factoring a negative Laurent summand",
                "Over any field, nonzero x and u satisfy the negative-index factorization for every natural c and k, including k=0.", DescribeRole.Theorem),
            Supplier("laurent_zero", "The zero-index Laurent term",
                "At index zero the literal summand is the product of the inverses of 1+embed(X) and 1+embed(A).", DescribeRole.Theorem),
            Supplier("zeroTerm_series", "The zero Laurent term comes from a rational power series",
                "For constant coefficient A(0)=1, the zero term is the Laurent embedding of (1+X) inverse times (1+map(A)) inverse over the rationals.", DescribeRole.Theorem),
            Node("ofSeries_inverse", "Laurent embedding preserves an inverse", OfSeriesInverseFormula(),
                "For a rational power series whose constant coefficient is nonzero, "
                + "ofPowerSeries sends its power-series inverse to its Laurent-series inverse."),
            Paragraph(Text("Paul D. Hanna's entries hanna2025a381362 and hanna2025a381363 "
                + "specify the same bilateral product equation with parameters c=2 and c=3. "
                + "Both conjecture a(n)=2 modulo four for every positive n. The common "
                + "normalization is A(0)=1.")),
            Paragraph(Text("The parameters c, k, n, N, K, and d are natural numbers; j is an "
                + "integer. A and B are integer power series. The operator iota embeds an "
                + "integer power series into rational Laurent series by mapping its "
                + "coefficients to the rationals and applying ofPowerSeries. The symbol "
                + "x denotes iota(X). Laurent powers have integer exponents. Exponents "
                + "in positiveTerm and negativeTerm are natural, including truncated "
                + "subtraction c*k-1. The operator natAbs is the natural absolute value. "
                + "The operation invOfUnit(F,1) uses the unit one for the constant coefficient; "
                + "all its uses as inverses below have constant coefficient one. The operator "
                + "mk constructs a power series from its coefficients.")),
            Node("bilateralTerm", "Integral nonzero-index terms", TermFormula(),
                "The zero term is isolated. For j=k>0 the original term contains X^k. "
                + "For j=-k<0, factoring the inverse powers gives X^(c*k^2) times the "
                + "displayed integral unit inverses. The negative factorization is also "
                + "proved as an identity in a field.", DescribeRole.Definition),
            Node("nonzeroSum", "The coefficientwise bilateral remainder", SumFormula(),
                "At degree N the remainder sums the integral terms over [-N,N]. "
                + "The following theorem proves independence of every larger window.",
                DescribeRole.Definition),
            Node("finite_window", "Every coefficient has a finite window", WindowFormula(),
                "A positive term has a factor X^k and a negative term has a factor "
                + "X^(c*k^2). For c at least two, either factor has degree at least k. "
                + "Thus every index outside [-N,N] vanishes at degree N. Extending "
                + "the finite sum only adds these zero coefficients."),
            Node("a", "Stabilized integral coefficients", SequenceFormula(),
                "Here P is the approximation sequence and G is the inverse "
                + "of 1+X. Differences of products, powers, and unit inverses preserve "
                + "agreement below degree d. Every nonzero-index term supplies another "
                + "factor X. The remainder has constant coefficient zero, so the "
                + "displayed iteration improves agreement to degree d+1.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The stabilized coefficients define an integer series for each natural c. "
                + "The assertions about its equation and uniqueness assume c at least two.",
                DescribeRole.Definition),
            Node("polynomial_form", "The normalized polynomial equation", PolynomialFormula(),
                "Stabilization gives a fixed point of the integral iteration. Multiplying "
                + "by 1+X gives the polynomial equation, and the zero constant coefficient "
                + "of the remainder gives the normalization."),
            Node("laurentTerm", "The literal bilateral summand", LaurentFormula(),
                "This is the summand in the two OEIS NAMEs, with c left arbitrary. "
                + "The zero term is (1+x)^(-1)*(1+iota(A))^(-1). For every nonzero "
                + "index the field factorization identifies it with iota(bilateralTerm).",
                DescribeRole.Definition),
            Node("generating_equation", "The defining Laurent-series equation", EquationFormula(),
                "The polynomial equation implies that the zero Laurent term plus the "
                + "embedded nonzero-index remainder is the constant one half. Coefficient "
                + "comparison and the finite-window theorem give the equality for every "
                + "N and every K at least N. This is the coefficientwise meaning of the "
                + "bilateral sum in the NAMEs."),
            Node("generating_unique", "Uniqueness for the literal equation", UniqueFormula(),
                "The zero Laurent term comes from a rational power series. Equality "
                + "of every nonnegative coefficient therefore recovers its power-series "
                + "identity with the remainder. Clearing the two unit denominators gives "
                + "the integral polynomial equation. Degree contraction then identifies "
                + "any normalized integer solution with generatingSeries(c)."),
            Node("hanna_conjecture_general", "The general coefficient congruence", GeneralFormula(),
                "Put H=nonzeroSum(c,A) and G=(1+X)^(-1). The fixed-point equation is "
                + "A=2*G-1+2*(1+A)*H. Setting B=G+(1+A)*H gives 1+A=2*B and then "
                + "A-(2*G-1)=4*B*H. The coefficient of G at n is (-1)^n. "
                + "For n>0, twice this coefficient has remainder two modulo four."),
            Node("hanna_conjecture_a381362", "Hanna's A381362 conjecture", InstanceFormula(D(2)),
                "The parameter c=2 gives A381362 and satisfies the general theorem's "
                + "parameter bound. The generating-equation and uniqueness theorems "
                + "identify these coefficients with the normalized series in hanna2025a381362.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceTwo),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381362-bilateral-product-quadratic-mod-four"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a381363", "Hanna's A381363 conjecture", InstanceFormula(D(3)),
                "The parameter c=3 gives A381363 and satisfies the general theorem's "
                + "parameter bound. The generating-equation and uniqueness theorems "
                + "identify these coefficients with the normalized series in hanna2025a381363.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceThree),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381363-bilateral-product-cubic-mod-four"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Supplier(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("bilateral-product-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(SupplierFormula(name)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("bilateral-product-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula SupplierFormula(string name)
    {
        Formula d = F.Id("d"), c = C(), k = F.Id("k"), n = F.Id("n");
        Formula a = F.Id("A"), b = F.Id("B"), f = F.Id("F"), g = F.Id("G");
        Formula Agree(Formula degree, Formula lhs, Formula rhs) => Call("Agree", degree, lhs, rhs);
        Formula Inv(Formula value) => Call("invOfUnit", value, D(1));
        Formula Embed(Formula value) => Call("embed", value);
        Formula Iff(Formula lhs, Formula rhs) => new Formula.Logic(
            Parenthesized(lhs), FormulaLogicOperator.Iff, Parenthesized(rhs));
        Formula Dvd(Formula lhs, Formula rhs) => Call("Dvd", lhs, rhs);
        Formula All(Formula body, params (string Name, Formula Type)[] variables) =>
            Seq(variables.Select(v => Bound(v.Name, v.Type)).Append(body).ToArray());
        Formula AgreementPair(Formula lhs, Formula rhs) => All(
            Implication(Agree(d, a, b), Implication(Agree(d, f, g), Agree(d, lhs, rhs))),
            ("d", Naturals()), ("A", Series()), ("B", Series()), ("F", Series()), ("G", Series()));
        Formula geometric = Named("geometric");
        Formula inverseGeometric = Inv(Add(D(1), X()));
        Formula ck = Mul(c, k), p = Mul(c, Power(k, D(2)));
        Formula positive = Mul(Power(X(), k), Mul(Mul(Power(a, k),
            Power(Add(Power(a, k), X()), Subtract(ck, D(1)))),
            Power(Add(Power(X(), k), a), Subtract(ck, D(1)))));
        Formula negative = Mul(Power(X(), p), Mul(Mul(Power(a, p),
            Power(Inv(Add(D(1), Mul(X(), Power(a, k)))), Add(ck, D(1)))),
            Power(Inv(Add(D(1), Mul(Power(X(), k), a))), Add(ck, D(1)))));
        Formula LaurentPowerInverse(Formula value) => Power(value, Negative(D(1)));
        Formula zeroTerm = Mul(LaurentPowerInverse(Add(D(1), Embed(X()))),
            LaurentPowerInverse(Add(D(1), Embed(a))));
        Formula RationalSeriesEmbed(Formula value) =>
            Call("HahnSeries.ofPowerSeries", Integers(), Rationals(), value);
        Formula Cast(Formula value) => Call("Int.cast", value);
        Formula result = name switch
        {
            "positiveTerm" => All(Equal(Call(name, c, a, k), positive),
                ("c", Naturals()), ("A", Series()), ("k", Naturals())),
            "negativeTerm" => All(Equal(Call(name, c, a, k), negative),
                ("c", Naturals()), ("A", Series()), ("k", Naturals())),
            "Agree" => All(Iff(Agree(d, a, b), All(
                Implication(Less(n, d), Equal(Coeff(n, a), Coeff(n, b))), ("n", Naturals()))),
                ("d", Naturals()), ("A", Series()), ("B", Series())),
            "agree_iff" => All(Iff(Agree(d, a, b), Dvd(Power(X(), d), Subtract(a, b))),
                ("d", Naturals()), ("A", Series()), ("B", Series())),
            "agree_refl" => All(Agree(d, a, a), ("d", Naturals()), ("A", Series())),
            "agree_add" => AgreementPair(Add(a, f), Add(b, g)),
            "agree_mul" => AgreementPair(Mul(a, f), Mul(b, g)),
            "agree_pow" => All(Implication(Agree(d, a, b), Agree(d, Power(a, k), Power(b, k))),
                ("d", Naturals()), ("A", Series()), ("B", Series()), ("k", Naturals())),
            "agree_inverse" => All(Implication(Equal(Constant(a), D(1)),
                Implication(Equal(Constant(b), D(1)),
                    Implication(Agree(d, a, b), Agree(d, Inv(a), Inv(b))))),
                ("d", Naturals()), ("A", Series()), ("B", Series())),
            "agree_shift" => All(Implication(Less(D(0), k),
                Implication(Agree(d, a, b), Agree(Add(d, D(1)),
                    Mul(Power(X(), k), a), Mul(Power(X(), k), b)))),
                ("d", Naturals()), ("k", Naturals()), ("A", Series()), ("B", Series())),
            "geometric" => Equal(geometric, inverseGeometric),
            "geometric_spec" => Equal(Mul(geometric, Add(D(1), X())), D(1)),
            "geometric_coeff" => All(Equal(Coeff(n, geometric), Power(Negative(D(1)), n)),
                ("n", Naturals())),
            "step" => All(Equal(Call(name, c, a), Add(Subtract(Mul(D(2), geometric), D(1)),
                Mul(D(2), Mul(Add(D(1), a), Rem(c, a))))), ("c", Naturals()), ("A", Series())),
            "approximation" => All(Conjunction(Equal(Call(name, c, D(0)), D(1)),
                All(Equal(Call(name, c, Add(d, D(1))), Call("step", c, Call(name, c, d))),
                    ("d", Naturals()))), ("c", Naturals())),
            "equation_iff" => All(Iff(Polynomial(a), Equal(a, Call("step", c, a))),
                ("c", Naturals()), ("A", Series())),
            "embed" => All(Equal(Embed(a), RationalSeriesEmbed(
                Call("PowerSeries.map", Call("Int.castRingHom", Rationals()), a))), ("A", Series())),
            "embed_coeff" => All(Equal(Call("HahnSeries.coeff", Embed(a), Call("Int.ofNat", n)),
                Cast(Coeff(n, a))), ("A", Series()), ("n", Naturals())),
            "embed_injective" => Call("Function.Injective", Named("embed")),
            "embed_inverse" => All(Implication(Equal(Constant(a), D(1)),
                Equal(Embed(Inv(a)), LaurentPowerInverse(Embed(a)))), ("A", Series())),
            "negative_factorization" => NegativeFactorizationFormula(),
            "laurent_zero" => All(Equal(LT(c, a, D(0)), zeroTerm), ("c", Naturals()), ("A", Series())),
            "zeroTerm_series" => All(Implication(Equal(Constant(a), D(1)),
                Equal(LT(c, a, D(0)), RationalSeriesEmbed(Mul(
                    LaurentPowerInverse(Add(D(1), X())),
                    LaurentPowerInverse(Add(D(1), Call("PowerSeries.map",
                        Call("Int.castRingHom", Rationals()), a))))))),
                ("c", Naturals()), ("A", Series())),
            _ => throw new ArgumentOutOfRangeException(nameof(name))
        };
        return Disp(result);
    }

    private static Formula NegativeFactorizationFormula()
    {
        Formula field = F.Id("F"), x = F.Id("x"), u = F.Id("u"), c = C(), k = F.Id("k");
        Formula ck = Mul(c, k), p = Mul(c, Power(k, D(2)));
        Formula nk = Negative(k), exponent = Negative(Add(ck, D(1)));
        Formula lhs = Mul(Mul(Mul(Power(x, nk), Power(u, nk)),
            Power(Add(Power(u, nk), x), exponent)), Power(Add(Power(x, nk), u), exponent));
        Formula Inv(Formula value) => Power(value, Negative(D(1)));
        Formula rhs = Mul(Power(x, p), Mul(Mul(Power(u, p),
            Power(Inv(Add(D(1), Mul(x, Power(u, k)))), Add(ck, D(1)))),
            Power(Inv(Add(D(1), Mul(Power(x, k), u))), Add(ck, D(1)))));
        Formula Nonzero(Formula value) => new Formula.Relation(value, FormulaRelationOperator.NotEqual, D(0));
        return Seq(Bound("F", Named("Type")), Bound("field", Call("Field", field)),
            Bound("x", field), Bound("u", field), Bound("c", Naturals()), Bound("k", Naturals()),
            Implication(Nonzero(x), Implication(Nonzero(u), Equal(lhs, rhs))));
    }

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Series() => Call("PowerSeries", Integers());
    private static Formula X() => F.Id("X");
    private static Formula C() => F.Id("c");
    private static Formula GS(Formula c) => Call("generatingSeries", c);
    private static Formula Rem(Formula c, Formula b) => Call("nonzeroSum", c, b);
    private static Formula Term(Formula c, Formula b, Formula j) => Call("bilateralTerm", c, b, j);
    private static Formula LT(Formula c, Formula b, Formula j) => Call("laurentTerm", c, b, j);
    private static Formula Named(string name) => Seq(Operatorname, Grp(Seq(
        name.Split('.').Select((part, index) =>
            index == 0 ? F.Id(part) : Seq(Dot, F.Id(part))).ToArray())));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula AtMost(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Subtract(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));
    private static Formula Power(Formula a, Formula b) => new Formula.Power(Parenthesized(a), b);
    private static Formula Negative(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula Coeff(Formula n, Formula a) => Call("coeff", n, a);
    private static Formula Constant(Formula a) => Call("constantCoeff", a);
    private static Formula Bound(string name, Formula type) => Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Lambda(string name, Formula body) => Parenthesized(Seq(
        F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula Implication(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Conjunction(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Disjunction(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula IfThenElse(Formula p, Formula a, Formula b) => Parenthesized(Seq(
        Named("if"), Sp, Parenthesized(p), Sp, Named("then"), Sp, a, Sp, Named("else"), Sp, b));
    private static Formula SumOver(string name, Formula set, Formula body) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(name), Sp, InMacro, Sp, set)), Sp, Parenthesized(body));
    private static Formula Window(Formula n) => Call("Icc", Negative(n), n);
    private static Formula Half() => new Formula.Fraction(D(1), D(2));

    private static Formula OfSeriesInverseFormula()
    {
        var b = F.Id("B");
        var rational = Seq(Mathbb, Grp(F.Id("Q")));
        var embedding = Seq(Operatorname, Grp(F.Id("HahnSeries")), Dot,
            Operatorname, Grp(F.Id("ofPowerSeries")));
        Formula Embed(Formula f) => new Formula.Apply(embedding, [Integers(), rational, f]);
        var inverseB = new Formula.Power(Parenthesized(b), Negative(D(1)));
        return Disp(Seq(Bound("B", Call("PowerSeries", rational)),
            Implication(new Formula.Relation(Call("constantCoeff", b), FormulaRelationOperator.NotEqual, D(0)),
                Equal(Embed(inverseB), new Formula.Power(Parenthesized(Embed(b)), Negative(D(1)))))));
    }

    private static Formula TermFormula()
    {
        Formula b = F.Id("A"), j = F.Id("j"), k = F.Id("k");
        Formula ck = Mul(C(), k), p = Mul(C(), Power(k, D(2)));
        Formula positive = Mul(Power(X(), k), Mul(Mul(Power(b, k),
            Power(Add(Power(b, k), X()), Subtract(ck, D(1)))),
            Power(Add(Power(X(), k), b), Subtract(ck, D(1)))));
        Formula negative = Mul(Power(X(), p), Mul(Mul(Power(b, p),
            Power(Call("invOfUnit", Add(D(1), Mul(X(), Power(b, k))), D(1)), Add(ck, D(1)))),
            Power(Call("invOfUnit", Add(D(1), Mul(Power(X(), k), b)), D(1)), Add(ck, D(1)))));
        return Disp(new Formula.Aligned([
            Seq(Bound("c", Naturals()), Bound("A", Series()), Bound("j", Integers()),
                Equal(Term(C(), b, j), IfThenElse(Equal(j, D(0)), D(0),
                    IfThenElse(Less(D(0), j), Call("positiveTerm", C(), b, Call("natAbs", j)),
                        Call("negativeTerm", C(), b, Call("natAbs", j)))))),
            Seq(Bound("c", Naturals()), Bound("A", Series()), Bound("k", Naturals()),
                Equal(Call("positiveTerm", C(), b, k), positive)),
            Seq(Bound("c", Naturals()), Bound("A", Series()), Bound("k", Naturals()),
                Equal(Call("negativeTerm", C(), b, k), negative))
        ]));
    }

    private static Formula SumFormula()
    {
        Formula b = F.Id("A"), n = F.Id("N"), j = F.Id("j");
        return Disp(Seq(Bound("c", Naturals()), Bound("A", Series()), Equal(Rem(C(), b),
            Call("mk", Lambda("N", SumOver("j", Window(n), Coeff(n, Term(C(), b, j))))))));
    }

    private static Formula WindowFormula()
    {
        Formula b = F.Id("A"), n = F.Id("N"), k = F.Id("K"), j = F.Id("j");
        Formula outside = Disjunction(Less(j, Negative(n)), Less(n, j));
        return Disp(Seq(Bound("c", Naturals()), Implication(AtMost(D(2), C()),
            Seq(Bound("A", Series()), Bound("N", Naturals()), Bound("K", Naturals()),
                Implication(AtMost(n, k), Conjunction(
                    Seq(Bound("j", Integers()), Implication(outside, Equal(Coeff(n, Term(C(), b, j)), D(0)))),
                    Equal(Coeff(n, Rem(C(), b)), SumOver("j", Window(k), Coeff(n, Term(C(), b, j))))))))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), g = F.Id("G");
        Formula p = Call("P", C(), d);
        return Disp(new Formula.Aligned([
            Equal(g, Call("invOfUnit", Add(D(1), X()), D(1))),
            Seq(Bound("c", Naturals()), Equal(Call("P", C(), D(0)), D(1))),
            Seq(Bound("c", Naturals()), Bound("d", Naturals()), Equal(Call("P", C(), Add(d, D(1))),
                Add(Subtract(Mul(D(2), g), D(1)), Mul(D(2), Mul(Add(D(1), p), Rem(C(), p)))))),
            Seq(Bound("c", Naturals()), Bound("n", Naturals()), Equal(Call("a", C(), n),
                Coeff(n, Call("P", C(), Add(n, D(1))))))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Seq(Bound("c", Naturals()),
        Equal(GS(C()), Call("mk", Lambda("n", Call("a", C(), F.Id("n")))))));

    private static Formula Polynomial(Formula b) => Equal(
        Mul(Mul(Add(D(1), X()), Add(D(1), b)), Subtract(D(1), Mul(D(2), Rem(C(), b)))), D(2));

    private static Formula PolynomialFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(2), C()), Conjunction(Equal(Constant(GS(C())), D(1)), Polynomial(GS(C()))))));

    private static Formula LaurentFormula()
    {
        Formula b = F.Id("A"), j = F.Id("j"), x = F.Id("x"), u = Call("iota", b);
        Formula e = Subtract(Mul(C(), j), D(1));
        return Disp(new Formula.Aligned([
            Seq(Bound("A", Series()), Equal(u, Call("ofPowerSeries", Integers(), Rationals(),
                Call("map", Call("intCastRingHom", Rationals()), b)))),
            Equal(x, Call("iota", X())),
            Seq(Bound("c", Naturals()), Bound("A", Series()), Bound("j", Integers()),
                Equal(LT(C(), b, j), Mul(Mul(Mul(Power(x, j), Power(u, j)),
                    Power(Add(Power(u, j), x), e)), Power(Add(Power(x, j), u), e))))
        ]));
    }

    private static Formula Equation(Formula b)
    {
        Formula n = F.Id("N"), k = F.Id("K"), j = F.Id("j");
        return Seq(Bound("N", Naturals()), Bound("K", Naturals()), Implication(AtMost(n, k),
            Equal(SumOver("j", Window(k), Coeff(n, LT(C(), b, j))), IfThenElse(Equal(n, D(0)), Half(), D(0)))));
    }

    private static Formula EquationFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(2), C()), Conjunction(Equal(Constant(GS(C())), D(1)), Equation(GS(C()))))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("c", Naturals()), Implication(AtMost(D(2), C()), Seq(Bound("B", Series()),
            Implication(Equal(Constant(b), D(1)), Implication(Equation(b), Equal(b, GS(C()))))))));
    }

    private static Formula Congruence(Formula c) => Equal(new Formula.Modulo(Call("a", c, F.Id("n")), D(4)), D(2));
    private static Formula GeneralFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(2), C()), Seq(Bound("n", Naturals()),
            Implication(Less(D(0), F.Id("n")), Congruence(C()))))));
    private static Formula InstanceFormula(Formula c) => Disp(Seq(Bound("n", Naturals()),
        Implication(Less(D(0), F.Id("n")), Congruence(c))));
}
