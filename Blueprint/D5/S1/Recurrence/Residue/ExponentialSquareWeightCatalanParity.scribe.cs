using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class ExponentialSquareWeightCatalanParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Residue/ExponentialSquareWeightCatalanParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/hanna2026a397242");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A397242 are odd exactly one below a power of two.",
        H("Exponential Square Weights and Catalan Parity"),
        Blocks(
            Paragraph(Text("The first conjecture in hanna2026a397242 concerns the equation "
                + "A=exp(L), where L=x+Sum (n^2-1)a(n)x^n/n^2 for n>=2. Its formal "
                + "differential reading is A(0)=1 and X A'=M A, with M=X L'. "
                + "The differential identity and rational uniqueness below use exactly "
                + "this reading. The two conjectures modulo three are separate statements.")),
            Paragraph(Text("Indices are natural numbers. Subtraction inside an index is "
                + "natural subtraction, whereas the factors n^2-1 use ring subtraction. "
                + "The functions a and d have integer values; int casts a natural number "
                + "to an integer, ratNat and ratInt cast to the rationals, and modTwo "
                + "casts an integer to ZMod(2). All displayed fractions are rational "
                + "division. The operator mk constructs a formal power series, coeff "
                + "extracts a coefficient, and derivative takes the formal derivative "
                + "over its indicated ring. The maps mapRat and mapTwo apply the canonical "
                + "integer-to-rational and integer-to-ZMod(2) ring homomorphisms. "
                + "The sets range(n) and Ico(r,n) mean 0<=j<n and r<=j<n.")),
            Paragraph(Text("The symbol K denotes the imported integer series "),
                Ref("D5/S1/Recurrence/Invariants/CatalanCompositionSquareParity.catalanSeries"),
                Text(". Its imported catalan_equation states K(0)=0, coeff(1,K)=1 "
                    + "and K=X+K^2; binary_catalan identifies the support of mapTwo(K) "
                    + "as the powers of two. This is the formal prerequisite for the "
                    + "Catalan identification and the parity theorem.")),
            Node("d", "Integral normalized coefficients", DFormula(),
                "The guarded recursion uses only smaller indices. Its base values are "
                + "d(0)=0 and d(1)=1.", DescribeRole.Definition),
            Node("a", "The coefficient sequence", AFormula(),
                "The constant coefficient is one. Every positive-index coefficient is "
                + "n times the integral normalized coefficient d(n).", DescribeRole.Definition),
            Node("d_recurrence", "The integral convolution recurrence", RecurrenceFormula(),
                "Removing the guards restricts the convolution to 2<=j<n. The coefficient "
                + "of d(n) is one, so the recurrence determines integers without division."),
            Node("a_eq", "The integral normalization", NormalizationFormula(),
                "At every positive index the defining branch gives a(n)=n d(n)."),
            Node("M", "The integral logarithmic derivative", MFormula(),
                "The series M has coefficients zero and one at degrees zero and one. "
                + "At every higher degree its coefficient is (n^2-1)d(n).", DescribeRole.Definition),
            Node("log_derivative_identity", "The formal exponential equation", IdentityFormula(),
                "Coefficient comparison separates the endpoints and linear term of M A. "
                + "The remaining convolution is the recurrence for d(n). Adding "
                + "(n^2-1)d(n) gives n^2 d(n), which is coefficient n of X A'. "
                + "The constant coefficient of A is one."),
            Node("coeff_M_rat", "The exact rational weights", RationalShapeFormula(),
                "For n>=2, substitution of a(n)=n d(n) and cancellation of the nonzero "
                + "rational n gives coefficient (n^2-1)a(n)/n. This is coefficient n "
                + "of X L' for the exponent in hanna2026a397242."),
            Node("generating_unique", "Uniqueness among rational solutions", UniqueFormula(),
                "Strong induction compares the two differential equations. Every interior "
                + "convolution term agrees at smaller indices. Degree one is forced to "
                + "one; at higher degrees clearing n from the remaining equation forces "
                + "equality of the nth coefficients."),
            Node("mod_two_catalan", "The decimated Catalan series", CatalanFormula(),
                "Reduction modulo two kills the convolution at even indices, giving "
                + "d(2m)=d(2m-1) for m>=1. Splitting the odd-index convolution into "
                + "even and odd summation indices then gives the Catalan recurrence for "
                + "e(m)=d(2m+1) in ZMod(2). Its series E satisfies E=1+X E^2. "
                + "Both X E and mapTwo(K) satisfy Y=X+Y^2 and have constant coefficient "
                + "zero. Their difference is annihilated by the unit 1-Y-Z, so they agree."),
            Node("hanna_conjecture", "The first A397242 conjecture", HannaFormula(),
                "At positive even indices the factor n makes a(n) even. At index "
                + "2m+1 the Catalan identity and imported binary support say that d(2m+1) "
                + "is odd exactly when m+1 is a power of two. Doubling translates this "
                + "to n+1 being a power of two. The constant coefficient corresponds to 2^0.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a397242-exponential-square-weight-catalan-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a397242-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula N() => F.Id("n");
    private static Formula J() => F.Id("j");
    private static Formula X() => F.Id("X");
    private static Formula MSeries() => F.Id("M");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));
    private static Formula Conjunction(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula AtLeast(Formula value, Formula bound) => Seq(bound, Sp, Le, Sp, value);
    private static Formula Conditional(Formula test, Formula yes, Formula no) => Parenthesized(Seq(
        Named("if"), Sp, Parenthesized(test), Sp, Named("then"), Sp, yes,
        Sp, Named("else"), Sp, no));
    private static Formula FunctionType(Formula domain, Formula codomain) => Seq(domain, Sp, To, Sp, codomain);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Sp, Mapsto, Sp, body));
    private static Formula Coefficient(Formula index, Formula series) => Call("coeff", index, series);
    private static Formula A(Formula index) => Call("a", index);
    private static Formula DAt(Formula index) => Call("d", index);
    private static Formula Int(Formula index) => Call("int", index);
    private static Formula RatNat(Formula index) => Call("ratNat", index);
    private static Formula RatInt(Formula value) => Call("ratInt", value);
    private static Formula ASeries() => Call("mk", Named("a"));
    private static Formula Factor(Formula index) => Subtract(Power(index, D(2)), D(1));
    private static Formula Sum(Formula set, Formula summand) => Seq(
        new Formula.Subscript(F.Sum, Seq(J(), Sp, InMacro, Sp, set)), Sp, Parenthesized(summand));
    private static Formula Summand() => Mul(Mul(Mul(Factor(Int(J())), Int(Subtract(N(), J()))),
        DAt(J())), DAt(Subtract(N(), J())));
    private static Formula RationalTerm(Formula index, Formula value) =>
        new Formula.Fraction(Mul(Factor(RatNat(index)), value), RatNat(index));
    private static Formula Equation(Formula series, Formula weights, Formula ring) =>
        Equal(Mul(X(), Call("derivative", ring, series)), Mul(weights, series));

    private static Formula DFormula()
    {
        Formula prior = Subtract(N(), D(1));
        Formula guard = Conjunction(AtLeast(J(), D(2)), Seq(J(), Sp, Lt, Sp, N()));
        Formula recurrence = Add(Mul(Int(prior), DAt(prior)),
            Sum(Call("range", N()), Conditional(guard, Summand(), D(0))));
        return Disp(new Formula.Aligned([
            Seq(Named("d"), Colon, Sp, FunctionType(Naturals(), Integers())),
            Seq(Bound("n", Naturals()), Equal(DAt(N()), Conditional(AtLeast(N(), D(2)),
                recurrence, Conditional(Equal(N(), D(1)), D(1), D(0)))))
        ]));
    }

    private static Formula AFormula() => Disp(new Formula.Aligned([
        Seq(Named("a"), Colon, Sp, FunctionType(Naturals(), Integers())),
        Seq(Bound("n", Naturals()), Equal(A(N()),
            Conditional(Equal(N(), D(0)), D(1), Mul(Int(N()), DAt(N())))))
    ]));

    private static Formula RecurrenceFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(2)), Equal(DAt(N()),
            Add(Mul(Int(Subtract(N(), D(1))), DAt(Subtract(N(), D(1)))),
                Sum(Call("Ico", D(2), N()), Summand()))))));

    private static Formula NormalizationFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(1)), Equal(A(N()), Mul(Int(N()), DAt(N()))))));

    private static Formula MFormula() => Disp(Seq(MSeries(), Colon, Sp,
        Call("PowerSeries", Integers()), Comma, Sp,
        Equal(MSeries(), Call("mk", Lambda("n", Conditional(Equal(N(), D(0)), D(0),
            Conditional(Equal(N(), D(1)), D(1), Mul(Factor(Int(N())), DAt(N())))))))));

    private static Formula IdentityFormula() => Disp(Conjunction(
        Equal(Coefficient(D(0), ASeries()), D(1)), Equation(ASeries(), MSeries(), Integers())));

    private static Formula RationalShapeFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(AtLeast(N(), D(2)), Equal(Coefficient(N(), Call("mapRat", MSeries())),
            RationalTerm(N(), RatInt(A(N())))))));

    private static Formula UniqueFormula()
    {
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula BAt(Formula index) => new Formula.Apply(b, [index]);
        Formula shape = Seq(Bound("n", Naturals()), Implication(AtLeast(N(), D(2)),
            Equal(Coefficient(N(), m), RationalTerm(N(), BAt(N())))));
        Formula conclusion = Seq(Bound("n", Naturals()), Equal(BAt(N()), RatInt(A(N()))));
        return Disp(Seq(Bound("b", FunctionType(Naturals(), Rationals())),
            Bound("m", Call("PowerSeries", Rationals())),
            Implication(Equal(BAt(D(0)), D(1)),
            Implication(Equal(Coefficient(D(0), m), D(0)),
            Implication(Equal(Coefficient(D(1), m), D(1)),
            Implication(shape, Implication(Equation(Call("mk", b), m, Rationals()), conclusion)))))));
    }

    private static Formula CatalanFormula() => Disp(Equal(
        Mul(X(), Call("mk", Lambda("m", Call("modTwo", DAt(Add(Mul(D(2), F.Id("m")), D(1))))))),
        Call("mapTwo", F.Id("K"))));

    private static Formula HannaFormula()
    {
        Formula k = F.Id("k");
        Formula support = Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
            Equal(Add(N(), D(1)), Power(D(2), k)));
        return Disp(Seq(Bound("n", Naturals()), Call("Odd", A(N())),
            Sp, Iff, Sp, Parenthesized(support)));
    }
}
