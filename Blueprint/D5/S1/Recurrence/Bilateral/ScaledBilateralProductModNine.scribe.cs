using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Bilateral;

internal sealed class ScaledBilateralProductModNineDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Bilateral/ScaledBilateralProductModNine.";
    private static readonly LibraryNoteRef SourceOne =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a381364");
    private static readonly LibraryNoteRef SourceTwo =
        LibraryNoteRef.Create("D5/L/ArithSums/hanna2025a381365");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Hanna's scaled bilateral product family has every positive coefficient equal to six modulo nine.",
        H("The Scaled Bilateral Product Family of A381364 and A381365"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's entries hanna2025a381364 and hanna2025a381365 "
                + "specify the same bilateral product equation with parameters c=1 and c=2. "
                + "Both conjecture a(n)=6 modulo nine for every positive n. The common "
                + "normalization is A(0)=1.")),
            Paragraph(Text("The parameters c, k, n, N, K, and d are natural numbers; j is an "
                + "integer. A and B are integer power series. The operator iota embeds an "
                + "integer power series into rational Laurent series by mapping its "
                + "coefficients to the rationals and applying ofPowerSeries. The symbol "
                + "x denotes iota(X). Laurent powers have integer exponents. Exponents "
                + "in positiveTerm and negativeTerm are natural, including truncated "
                + "subtraction c*k-1. The operator natAbs is the natural absolute value. "
                + "The operation invOfUnit(F,1) uses the unit one for the constant coefficient; "
                + "on nonzero-index branches its arguments have constant coefficient one. The operator "
                + "mk constructs a power series from its coefficients. The operator div denotes "
                + "integer division and mod is integer remainder. Integer casts of natural "
                + "indices and parameters are implicit in Laurent exponents and coefficients.")),
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
                + "X^(c*k^2). For c at least one, either factor has degree at least k. "
                + "Thus every index outside [-N,N] vanishes at degree N. Extending "
                + "the finite sum only adds these zero coefficients."),
            Node("a", "Stabilized integral coefficients", SequenceFormula(),
                "Here P is the private approximation sequence and G is the inverse "
                + "of 1+2*X. For c at least one, pairing indices k and -k gives an even remainder: both terms "
                + "reduce to X^(c*k^2)*A^(c*k^2) modulo two. Thus halfSum is exact "
                + "coefficientwise division by two. Differences of products, powers, and unit inverses preserve "
                + "agreement below degree d. Every nonzero-index term supplies another "
                + "factor X. The remainder has constant coefficient zero, so the "
                + "displayed iteration improves agreement to degree d+1.", DescribeRole.Definition),
            Node("generatingSeries", "The generating series", GeneratingFormula(),
                "The diagonal coefficients define an integer series for each natural c. "
                + "Stabilization and the assertions about its equation and uniqueness assume c at least one.",
                DescribeRole.Definition),
            Node("polynomial_form", "The normalized polynomial equation", PolynomialFormula(),
                "Stabilization gives a fixed point of the integral iteration. Multiplying "
                + "by 1+2*X and using nonzeroSum=2*halfSum gives the polynomial equation. The zero constant coefficient "
                + "of the remainder gives the normalization."),
            Node("laurentTerm", "The literal bilateral summand", LaurentFormula(),
                "This is the summand in the two OEIS NAMEs, with c left arbitrary. "
                + "The zero term is (1+2*x)^(-1)*(1+2*iota(A))^(-1). When c is at least one "
                + "and constantCoeff(A)=1, the field factorization identifies every nonzero "
                + "index term with iota(bilateralTerm).",
                DescribeRole.Definition),
            Node("generating_equation", "The defining Laurent-series equation", EquationFormula(),
                "The polynomial equation implies that the zero Laurent term plus the "
                + "embedded nonzero-index remainder is the constant one third. Coefficient "
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
                "Put A=generatingSeries(c), J=halfSum(c,A), and G=(1+2*X)^(-1). "
                + "Recovering the polynomial form from the literal generating equation gives "
                + "A=1-3*X*G+3*(1+2*A)*J. Setting B=-X*G+(1+2*A)*J gives "
                + "A=1+3*B, hence 1+2*A=3*(1+2*B) and "
                + "A-(1-3*X*G)=9*(1+2*B)*J. At n=m+1 the coefficient of "
                + "1-3*X*G is -3*(-2)^m. Since (-2)^m is one modulo three, "
                + "this coefficient has remainder six modulo nine."),
            Node("hanna_conjecture_a381364", "Hanna's A381364 conjecture", InstanceFormula(D(1)),
                "The parameter c=1 gives A381364 and satisfies the general theorem's "
                + "parameter bound. The generating-equation and uniqueness theorems "
                + "identify these coefficients with the normalized series in hanna2025a381364.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceOne),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381364-scaled-bilateral-product-linear-mod-nine"),
                    ResolutionKind.Proved)),
            Node("hanna_conjecture_a381365", "Hanna's A381365 conjecture", InstanceFormula(D(2)),
                "The parameter c=2 gives A381365 and satisfies the general theorem's "
                + "parameter bound. The generating-equation and uniqueness theorems "
                + "identify these coefficients with the normalized series in hanna2025a381365.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(SourceTwo),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a381365-scaled-bilateral-product-quadratic-mod-nine"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("scaled-bilateral-product-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

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
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
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
    private static Formula Third() => new Formula.Fraction(D(1), D(3));

    private static Formula TermFormula()
    {
        Formula b = F.Id("A"), j = F.Id("j"), k = F.Id("k");
        Formula ck = Mul(C(), k), p = Mul(C(), Power(k, D(2)));
        Formula positive = Mul(Power(X(), k), Mul(Mul(Power(b, k),
            Power(Add(Power(b, k), Mul(D(2), X())), Subtract(ck, D(1)))),
            Power(Add(Power(X(), k), Mul(D(2), b)), Subtract(ck, D(1)))));
        Formula negative = Mul(Power(X(), p), Mul(Mul(Power(b, p),
            Power(Call("invOfUnit", Add(D(1), Mul(Mul(D(2), X()), Power(b, k))), D(1)), Add(ck, D(1)))),
            Power(Call("invOfUnit", Add(D(1), Mul(Mul(D(2), Power(X(), k)), b)), D(1)), Add(ck, D(1)))));
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
        return Disp(Seq(Bound("c", Naturals()), Implication(AtMost(D(1), C()),
            Seq(Bound("A", Series()), Bound("N", Naturals()), Bound("K", Naturals()),
                Implication(AtMost(n, k), Conjunction(
                    Seq(Bound("j", Integers()), Implication(outside, Equal(Coeff(n, Term(C(), b, j)), D(0)))),
                    Equal(Coeff(n, Rem(C(), b)), SumOver("j", Window(k), Coeff(n, Term(C(), b, j))))))))));
    }

    private static Formula SequenceFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), g = F.Id("G"), b = F.Id("A");
        Formula p = Call("P", C(), d);
        return Disp(new Formula.Aligned([
            Equal(g, Call("invOfUnit", Add(D(1), Mul(D(2), X())), D(1))),
            Seq(Bound("c", Naturals()), Bound("A", Series()),
                Equal(Call("halfSum", C(), b), Call("mk", Lambda("n",
                    Call("div", Coeff(n, Rem(C(), b)), D(2)))))),
            Seq(Bound("c", Naturals()), Equal(Call("P", C(), D(0)), D(1))),
            Seq(Bound("c", Naturals()), Bound("d", Naturals()), Equal(Call("P", C(), Add(d, D(1))),
                Add(Subtract(D(1), Mul(Mul(D(3), X()), g)),
                    Mul(D(3), Mul(Add(D(1), Mul(D(2), p)), Call("halfSum", C(), p)))))),
            Seq(Bound("c", Naturals()), Bound("n", Naturals()), Equal(Call("a", C(), n),
                Coeff(n, Call("P", C(), Add(n, D(1))))))
        ]));
    }

    private static Formula GeneratingFormula() => Disp(Seq(Bound("c", Naturals()),
        Equal(GS(C()), Call("mk", Lambda("n", Call("a", C(), F.Id("n")))))));

    private static Formula Polynomial(Formula b) => Equal(
        Mul(Mul(Add(D(1), Mul(D(2), X())), Add(D(1), Mul(D(2), b))),
            Subtract(D(1), Mul(D(3), Rem(C(), b)))), D(3));

    private static Formula PolynomialFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(1), C()), Conjunction(Equal(Constant(GS(C())), D(1)), Polynomial(GS(C()))))));

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
                    Power(Add(Power(u, j), Mul(D(2), x)), e)), Power(Add(Power(x, j), Mul(D(2), u)), e))))
        ]));
    }

    private static Formula Equation(Formula b)
    {
        Formula n = F.Id("N"), k = F.Id("K"), j = F.Id("j");
        return Seq(Bound("N", Naturals()), Bound("K", Naturals()), Implication(AtMost(n, k),
            Equal(SumOver("j", Window(k), Coeff(n, LT(C(), b, j))), IfThenElse(Equal(n, D(0)), Third(), D(0)))));
    }

    private static Formula EquationFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(1), C()), Conjunction(Equal(Constant(GS(C())), D(1)), Equation(GS(C()))))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("B");
        return Disp(Seq(Bound("c", Naturals()), Implication(AtMost(D(1), C()), Seq(Bound("B", Series()),
            Implication(Equal(Constant(b), D(1)), Implication(Equation(b), Equal(b, GS(C()))))))));
    }

    private static Formula Congruence(Formula c) => Equal(new Formula.Modulo(Call("a", c, F.Id("n")), D(9)), D(6));
    private static Formula GeneralFormula() => Disp(Seq(Bound("c", Naturals()),
        Implication(AtMost(D(1), C()), Seq(Bound("n", Naturals()),
            Implication(Less(D(0), F.Id("n")), Congruence(C()))))));
    private static Formula InstanceFormula(Formula c) => Disp(Seq(Bound("n", Naturals()),
        Implication(Less(D(0), F.Id("n")), Congruence(c))));
}
