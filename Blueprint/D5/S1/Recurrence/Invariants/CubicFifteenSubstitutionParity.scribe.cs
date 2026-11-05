using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CubicFifteenSubstitutionParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/CubicFifteenSubstitutionParity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/hanna2026a392525");
    private static readonly LibraryNoteRef FrobeniusSource =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/mathlib2026powerseriesfrobenius");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficients of OEIS A392525 are odd exactly at powers of two.",
        H("Hanna's Cubic Substitution Parity Conjecture"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A392525 entry gives the functional "
                + "equation and parity conjecture recorded in hanna2026a392525. "
                + "Formula (1), A(X)^3 = A(X^3 + 15 X A(X)^3), is used as the "
                + "defining equation, with constant coefficient zero and linear "
                + "coefficient one. It is the cubed form of the NAME under this "
                + "normalization; the cube-root operation itself is not formalized. "
                + "The separate conjecture modulo ten is not asserted.")),
            Paragraph(Text("PowerSeries(R) is the formal power-series ring with "
                + "indeterminate X, and subst(f,g) means f composed with g. All powers "
                + "are ordinary powers. Coefficient indices and exponents are natural "
                + "numbers. The operator mk constructs a series from its coefficient "
                + "function, and choose selects a witness of the displayed proved "
                + "existential proposition. The auxiliary series has coefficients in "
                + "ZMod(2); generatingSeries and a have integer coefficients.")),
            Node("prime_power_subst", "Frobenius as monomial substitution", PrimePowerFormula(),
                "For any prime p, raising a series over ZMod(p) to p equals substitution of X to the power p. PowerSeries.subst takes the inner series as its first argument.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(FrobeniusSource)),
            Node("powerTwoSeries", "The power-of-two series", PowerTwoFormula(),
                "Coefficient n is one in ZMod(2) precisely when n is a power of two, "
                + "and is zero otherwise. In particular the constant coefficient is "
                + "zero and the linear coefficient is one.", DescribeRole.Definition),
            Node("thue_series_equation", "The characteristic-two cubic identity", ThueFormula(),
                "Frobenius and halving a power-of-two exponent give C = X + C squared. "
                + "Put t = X cubed + X C cubed. Polynomial algebra shows that C cubed "
                + "satisfies Y + Y squared = t. Substitution into the quadratic "
                + "identity shows that C(t) satisfies the same equation. Two solutions "
                + "u and v with zero constant coefficients satisfy "
                + "(u-v)(1+u+v)=0. The second factor has constant coefficient one, "
                + "so absence of zero divisors forces u=v. Here C denotes powerTwoSeries."),
            Node("power_two_one", "The power-of-two series has linear coefficient one",
                Disp(Equal(Call("coeff", D(1), PowerTwo()), D(1))),
                "One is the zeroth power of two, so the linear coefficient is one."),
            Node("agree_iff", "Coefficient agreement as divisibility", PubAgreeIff(),
                "Two series agree below degree n exactly when their difference is divisible by X to the power n."),
            Node("agree_pow", "Powers preserve coefficient agreement", PubAgreePow(),
                "Divisibility of a difference implies divisibility of the corresponding power difference."),
            Node("agree_subst_order", "Substitution with a prescribed order", PubAgreeSubstitution(),
                "Outer agreement below n and inner divisibility by X to the power d imply agreement of the substitutions below m whenever m is at most d times n and the two inner series agree below m."),
            Node("power_two_zero", "The power-of-two series has zero constant coefficient", PowerTwoZeroFormula(),
                "Zero is not a power of two, so the constant coefficient of powerTwoSeries vanishes."),
            Node("generatingSeries", "The normalized integer solution", GeneratingFormula(),
                "Starting from X, correct coefficient n by the negative of the "
                + "degree-(n+2) residual coefficient divided by three using integer "
                + "division. Modulo three, Frobenius identifies the cube with "
                + "substitution of X cubed, and the factor fifteen vanishes. Every "
                + "residual coefficient is therefore divisible by three. Corrections "
                + "preserve earlier coefficients and remove the next error; their "
                + "stabilized coefficients prove the displayed existence proposition.",
                DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The value a(n) is coefficient n of the constructed generating series. "
                + "Its normalization gives a(0)=0 and a(1)=1.", DescribeRole.Definition),
            Node("generating_equation", "The functional equation and normalization", EquationFormula(),
                "The selected witness satisfies both normalization conditions and "
                + "the exact cubic functional equation of OEIS A392525. The identity "
                + "holds at every degree by stabilization of the corrected approximations."),
            Node("generating_unique", "Uniqueness of the integer solution", UniqueFormula(),
                "For normalized series agreeing below n, their cubes differ at "
                + "degree n+2 by three times their degree-n coefficient difference. "
                + "Their substituted right sides agree through degree n+2, since the "
                + "inner series is divisible by X cubed and its change is divisible "
                + "by X to the power n+3. The first-difference formula and strong "
                + "induction prove uniqueness over the integers."),
            Node("hanna_conjecture", "The A392525 parity conjecture", ConjectureFormula(),
                "Map the proved integer functional equation into ZMod(2), where "
                + "fifteen equals one and three is nonzero. The same first-difference "
                + "argument proves uniqueness there. The characteristic-two identity "
                + "therefore identifies the mapped generating series with powerTwoSeries. "
                + "The integer-cast parity equivalence proves the conjecture for every "
                + "positive index.", DescribeRole.Theorem,
                AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a392525-cubic-fifteen-substitution-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a392525-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula PrimePowerFormula() => Disp(Seq(Bound("p", Naturals()),
        OpenBracket, Call("Fact", new Formula.Apply(Seq(Named("Nat"), Dot, Named("Prime")), [F.Id("p")])), CloseBracket, Comma, Sp,
        Bound("f", Series(Call("ZMod", F.Id("p")))),
        Equal(Power(F.Id("f"), F.Id("p")), new Formula.Apply(
            Seq(Named("PowerSeries"), Dot, Named("subst")), [Power(X(), F.Id("p")), F.Id("f")]))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula ModTwo() => Call("ZMod", D(2));
    private static Formula Series(Formula ring) => Call("PowerSeries", ring);
    private static Formula X() => F.Id("X");
    private static Formula Generating() => Named("generatingSeries");
    private static Formula PowerTwo() => Named("powerTwoSeries");
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula IsPowerTwo(Formula n) => Seq(
        Exists, Sp, F.Id("k"), Colon, Sp, Naturals(), Comma, Sp,
        Equal(n, Power(D(2), F.Id("k"))));
    private static Formula CubicEquation(Formula f) => Equal(Power(f, D(3)),
        Call("subst", f, Add(Power(X(), D(3)), Mul(Mul(D(1, 5), X()), Power(f, D(3))))));
    private static Formula NormalizedEquation(Formula f) =>
        And(Equal(Call("constantCoeff", f), D(0)),
            And(Equal(Call("coeff", D(1), f), D(1)), CubicEquation(f)));

    private static Formula PowerTwoFormula() => Disp(Equal(PowerTwo(),
        Call("mk", Parenthesized(Seq(F.Id("n"), Colon, Sp, Naturals(), Sp, Mapsto, Sp,
            Named("if"), Sp, Parenthesized(IsPowerTwo(F.Id("n"))), Sp, Named("then"), Sp,
            Parenthesized(Seq(D(1), Colon, Sp, ModTwo())), Sp, Named("else"), Sp,
            Parenthesized(Seq(D(0), Colon, Sp, ModTwo())))))));

    private static Formula ThueFormula() => Disp(And(
        Equal(PowerTwo(), Add(X(), Power(PowerTwo(), D(2)))),
        Equal(Power(PowerTwo(), D(3)), Call("subst", PowerTwo(),
            Add(Power(X(), D(3)), Mul(X(), Power(PowerTwo(), D(3))))))));

    private static Formula GeneratingFormula() => Disp(Equal(Generating(),
        Call("choose", Seq(Exists, Sp, F.Id("f"), Colon, Sp, Series(Integers()), Comma, Sp,
            Parenthesized(NormalizedEquation(F.Id("f")))))));

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", F.Id("n")), Call("coeff", F.Id("n"), Generating()))));

    private static Formula EquationFormula() => Disp(NormalizedEquation(Generating()));

    private static Formula UniqueFormula() => Disp(Seq(Bound("f", Series(Integers())),
        Implication(Equal(Call("constantCoeff", F.Id("f")), D(0)),
            Implication(Equal(Call("coeff", D(1), F.Id("f")), D(1)),
                Implication(CubicEquation(F.Id("f")), Equal(F.Id("f"), Generating()))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Seq(D(1), Sp, Le, Sp, F.Id("n")),
            Parenthesized(Seq(Call("Odd", Call("a", F.Id("n"))), Sp, Iff, Sp,
                Parenthesized(IsPowerTwo(F.Id("n"))))))));
    private static Formula PowerTwoZeroFormula() =>
        Disp(Equal(Call("constantCoeff", PowerTwo()), D(0)));


    private static Formula PubV(string name) => F.Id(name);
    private static Formula PubSeries() => Call("PowerSeries", PubV("R"));
    private static Formula PubAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, PubV(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula PubRel(Formula a, Formula op, Formula b) => Seq(a, Sp, op, Sp, b);
    private static Formula PubImp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula PubEq(Formula a, Formula b) => PubRel(a, Eq, b);
    private static Formula PubRing(Formula body) => PubAll("R", Named("Type"),
        Seq(OpenBracket, Call("CommRing", PubV("R")), CloseBracket, Comma, Sp, body));
    private static Formula PubAgree(Formula n, Formula f, Formula g) => PubAll("k", Naturals(),
        PubImp(PubRel(PubV("k"), Lt, n), PubEq(Call("coeff", PubV("k"), f), Call("coeff", PubV("k"), g))));
    private static Formula PubFG(Formula body) => PubAll("f", PubSeries(), PubAll("g", PubSeries(), body));
    private static Formula PubAgreeIff() => Disp(PubRing(PubAll("n", Naturals(), PubFG(
        Seq(Parenthesized(PubAgree(PubV("n"), PubV("f"), PubV("g"))), Sp, Iff, Sp,
            Parenthesized(PubRel(Power(X(), PubV("n")), Mid,
                new Formula.Binary(PubV("f"), FormulaBinaryOperator.Subtract, PubV("g")))))))));
    private static Formula PubAgreePow() => Disp(PubRing(PubAll("n", Naturals(), PubFG(
        PubImp(PubAgree(PubV("n"), PubV("f"), PubV("g")), PubAll("j", Naturals(),
            PubAgree(PubV("n"), Power(PubV("f"), PubV("j")), Power(PubV("g"), PubV("j")))))))));
    private static Formula PubAgreeSubstitution() => Disp(PubRing(PubAll("n", Naturals(),
        PubAll("m", Naturals(), PubAll("d", Naturals(), PubFG(PubAll("u", PubSeries(), PubAll("v", PubSeries(),
            PubImp(PubEq(Call("constantCoeff", PubV("u")), D(0)),
            PubImp(PubEq(Call("constantCoeff", PubV("v")), D(0)),
            PubImp(PubRel(Power(X(), PubV("d")), Mid, PubV("u")),
            PubImp(PubRel(Power(X(), PubV("d")), Mid, PubV("v")),
            PubImp(PubRel(PubV("m"), Le, Mul(PubV("d"), PubV("n"))),
            PubImp(PubAgree(PubV("n"), PubV("f"), PubV("g")),
            PubImp(PubAgree(PubV("m"), PubV("u"), PubV("v")),
                PubAgree(PubV("m"), new Formula.Apply(Seq(Named("PowerSeries"), Dot, Named("subst")), [PubV("u"), PubV("f")]),
                    new Formula.Apply(Seq(Named("PowerSeries"), Dot, Named("subst")), [PubV("v"), PubV("g")])))))))))))))))));
}
