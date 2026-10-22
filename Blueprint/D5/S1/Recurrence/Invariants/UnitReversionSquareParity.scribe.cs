using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class UnitReversionSquareParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Invariants/UnitReversionSquareParity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized integer solution of Hanna's A373312 equation has odd coefficients exactly at positive Mersenne indices.",
        H("Unit Reversion and Square Parity"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS entry hanna2024a373312 specifies "
                + "A(x)^2=A(x*A(x)/(1-A(x))^2) and conjectures that a(n) is odd exactly "
                + "when n=2^k-1 for k at least one. The normalization is A(0)=0 and a(1)=1.")),
            Paragraph(Text("Here A denotes generatingSeries and U denotes innerSeries. "
                + "PowerSeries(R) denotes formal power series over R, X is the indeterminate, "
                + "coeff(n,f) extracts coefficient n, and mk builds a series from a coefficient "
                + "function. The notation subst(f,g) means f composed with g. The operation "
                + "invOfUnit(f,1) is the power-series inverse with prescribed constant unit 1; "
                + "every denominator used below has constant coefficient 1. The auxiliary "
                + "P(n), r(f), and q(f) in the construction are integer power series. Indices "
                + "and exponents are natural numbers, including subtraction in 2^k-1; a(n) "
                + "is an integer. In the mod-two identity X and the arithmetic lie over ZMod(2).")),
            Node("square_subst", "Squaring in characteristic two", PublishedSquareSubstitution(),
                "Squaring a series over ZMod(2) substitutes X squared for X."),
            Node("lacunary_coeff", "The lacunary coefficient criterion", PublishedLacunaryCoefficients(),
                "A zero-constant series with linear coefficient one satisfying f = X + X*f.subst(X^2) "
                + "has coefficient one exactly at the positive Mersenne indices."),
            Node("Agree", "Agreement of coefficient prefixes", PublishedAgreeFormula(),
                "Two series agree below d when their coefficients at every natural index less than d coincide.", DescribeRole.Definition),
            Node("agree_pow", "Powers preserve agreement", PublishedPowerFormula(),
                "The difference of powers is divisible by the difference of the original series."),
            Node("agree_mul", "Products preserve agreement", PublishedProductFormula(),
                "The difference of products is a sum of two multiples of the original differences."),
            Node("agree_iff", "Agree iff",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("d"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Call("Agree", F.Id("d"), F.Id("f"), F.Id("g"))), Sp, Iff, Sp, Parenthesized(Seq(new Formula.Power(Parenthesized(F.Id("X")), F.Id("d")), Sp, Mid, Sp, new Formula.Binary(Parenthesized(F.Id("f")), FormulaBinaryOperator.Subtract, Parenthesized(F.Id("g")))))))))))),
                "Coefficient agreement is divisibility of the difference by X to the power d.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("agree_mono", "Agree mono",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("d"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("e"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Call("Agree", F.Id("d"), F.Id("f"), F.Id("g"))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(F.Id("e"), Sp, Le, Sp, F.Id("d"))), Sp, Implies, Sp, Parenthesized(Call("Agree", F.Id("e"), F.Id("f"), F.Id("g"))))))))))))),
                "Agreement persists on a smaller range of degrees.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("agree_X", "Agree x",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("d"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Call("Agree", F.Id("d"), F.Id("f"), F.Id("g"))), Sp, Implies, Sp, Parenthesized(Call("Agree", new Formula.Binary(Parenthesized(F.Id("d")), FormulaBinaryOperator.Add, Parenthesized(D(1))), new Formula.Binary(Parenthesized(F.Id("X")), FormulaBinaryOperator.Multiply, Parenthesized(F.Id("f"))), new Formula.Binary(Parenthesized(F.Id("X")), FormulaBinaryOperator.Multiply, Parenthesized(F.Id("g")))))))))))),
                "Multiplication by X increases the degree of agreement by one.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("subst_outer_agree", "Subst outer agree",
                Disp(Seq(Forall, Sp, F.Id("R"), Colon, Sp, F.Id("Type"), Comma, Sp, Seq(OpenBracket, Call("CommRing", F.Id("R")), CloseBracket, Comma, Sp, Seq(Forall, Sp, F.Id("d"), Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp, Seq(Forall, Sp, F.Id("f"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("g"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Forall, Sp, F.Id("u"), Colon, Sp, Call("PowerSeries", F.Id("R")), Comma, Sp, Seq(Parenthesized(Call("Agree", F.Id("d"), F.Id("f"), F.Id("g"))), Sp, Implies, Sp, Parenthesized(Seq(Parenthesized(Seq(new Formula.Power(Parenthesized(F.Id("X")), D(2)), Sp, Mid, Sp, F.Id("u"))), Sp, Implies, Sp, Parenthesized(Call("Agree", new Formula.Binary(Parenthesized(D(2)), FormulaBinaryOperator.Multiply, Parenthesized(F.Id("d"))), Call("subst", F.Id("f"), F.Id("u")), Call("subst", F.Id("g"), F.Id("u")))))))))))))),
                "Substitution by a series divisible by X squared doubles outer coefficient agreement.", DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("subst_inner_agree", "Agreement of inner substitutions", PublishedInnerAgreementFormula(),
                "In this formula subst(u,f) means f(u). Substitution into the same outer series preserves agreement of zero-constant inner series."),
            Node("subst_constant", "Constant coefficient of a composition", PublishedConstantFormula(),
                "In this formula subst(u,f) means f(u). Composing with a zero-constant series preserves the outer series' constant coefficient."),
            Node("generatingSeries", "Construction of the integer series", GeneratingFormula(),
                "Write A=X*B. The equation B=r(B)^2*subst(B,q(B)) contracts agreement "
                + "by one degree for series of constant coefficient 1. The inverse r(B) "
                + "gains a degree of agreement, while q(B) has order at least two, so "
                + "outer substitution doubles the degree of agreement. Consequently "
                + "coefficient n of P(n) has stabilized, and these coefficients define B.",
                DescribeRole.Definition),
            Node("a", "The integer coefficient sequence", CoefficientFormula(),
                "The sequence is defined by coefficient extraction from A.",
                DescribeRole.Definition),
            Node("innerSeries", "The unit-denominator argument", InnerFormula(),
                "Since A has zero constant coefficient, 1-A is a unit. Mathlib's "
                + "invOfUnit_mul identifies the prescribed inverse with the denominator "
                + "in Hanna's functional equation.", DescribeRole.Definition),
            Node("generating_equation", "The normalized generating equation", EquationFormula(),
                "Stabilization gives B=r(B)^2*subst(B,q(B)). Multiplication by X^2*B "
                + "and the substitution multiplication law give A^2=subst(A,U). The "
                + "initial constant coefficient of B is 1, giving both normalization identities."),
            Node("generating_unique", "Uniqueness over the integers", UniqueFormula(),
                "The zero constant coefficient gives f=X*B, and the linear coefficient "
                + "gives B(0)=1. Cancellation of the nonzero factor X^2*B turns the "
                + "functional equation into the same contracting fixed-point equation. "
                + "Induction on the degree of agreement identifies B with the constructed series."),
            Node("mod_two_fixed", "The lacunary fixed-point equation", ModTwoFormula(),
                "Map the proved generating equation to ZMod(2). Frobenius identifies "
                + "A^2 with subst(A,X^2). Mathlib's compositional inverse cancels the "
                + "outer series A, whose linear coefficient is 1, and gives U=X^2. "
                + "Clearing the unit denominator and cancelling X yields A=X*(1-A)^2. "
                + "Characteristic two and Frobenius give the displayed equation."),
            Node("hanna_conjecture", "Hanna's parity conjecture", ConjectureFormula(),
                "The fixed-point equation gives coefficient 1 equal to 1. For n positive, "
                + "coefficient n+1 is zero when n is odd, and is coefficient n/2 when n "
                + "is even. The index n+1 is a positive Mersenne index exactly when "
                + "n is even and n/2 is a positive Mersenne index. Strong induction, "
                + "with constant coefficient zero, proves the support classification. "
                + "An integer maps to 1 in ZMod(2) exactly when it is odd.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Arith/hanna2024a373312")),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a373312-unit-reversion-square-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role = DescribeRole.Theorem, AssessedProvenance? provenance = null,
        OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("unit-reversion-square-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula A() => F.Id("A");
    private static Formula U() => F.Id("U");
    private static Formula X() => F.Id("X");
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(Parenthesized(value), exponent);
    private static Formula Bound(string name, Formula type) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, conclusion);
    private static Formula Positive(Formula value) => Seq(D(1), Sp, Le, Sp, value);
    private static Formula And(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Land, Sp, Parenthesized(right));
    private static Formula Function(string name, Formula body) =>
        Parenthesized(Seq(F.Id(name), Colon, Sp, Naturals(), Sp, Mapsto, Sp, body));
    private static Formula P(Formula index) => Call("P", index);
    private static Formula Reciprocal(Formula series) =>
        Call("invOfUnit", Subtract(D(1), series), D(1));
    private static Formula Inner(Formula series) =>
        Mul(Mul(X(), series), Power(Reciprocal(series), D(2)));
    private static Formula Reduced() => Call("map", Call("intCastRingHom", Call("ZMod", D(2))), A());

    private static Formula GeneratingFormula()
    {
        Formula f = F.Id("f");
        return Disp(new Formula.Aligned([
            Seq(Bound("f", Call("PowerSeries", Integers())),
                Equal(Call("r", f), Reciprocal(Mul(X(), f)))),
            Seq(Bound("f", Call("PowerSeries", Integers())),
                Equal(Call("q", f), Mul(Mul(Power(X(), D(2)), f), Power(Call("r", f), D(2))))),
            Equal(P(D(0)), D(1)),
            Seq(Bound("n", Naturals()), Equal(P(Add(N(), D(1))),
                Mul(Power(Call("r", P(N())), D(2)), Call("subst", P(N()), Call("q", P(N())))))),
            Equal(A(), Mul(X(), Call("mk", Function("n", Call("coeff", N(), P(N()))))))
        ]));
    }

    private static Formula CoefficientFormula() => Disp(Seq(Bound("n", Naturals()),
        Equal(Call("a", N()), Call("coeff", N(), A()))));

    private static Formula InnerFormula() => Disp(Equal(U(), Inner(A())));

    private static Formula EquationFormula() => Disp(And(
        Equal(Call("constantCoeff", A()), D(0)), And(
            Equal(Call("coeff", D(1), A()), D(1)),
            Equal(Power(A(), D(2)), Call("subst", A(), U())))));

    private static Formula UniqueFormula()
    {
        Formula f = F.Id("f");
        return Disp(Seq(Bound("f", Call("PowerSeries", Integers())),
            Implication(Equal(Call("constantCoeff", f), D(0)),
                Implication(Equal(Call("coeff", D(1), f), D(1)),
                    Implication(Equal(Power(f, D(2)), Call("subst", f, Inner(f))),
                        Equal(f, A()))))));
    }

    private static Formula ModTwoFormula() => Disp(Equal(Reduced(),
        Add(X(), Mul(X(), Call("subst", Reduced(), Power(X(), D(2)))))));

    private static Formula ConjectureFormula() => Disp(Seq(Bound("n", Naturals()),
        Implication(Positive(N()), Parenthesized(Seq(Call("Odd", Call("a", N())), Sp, Iff, Sp,
            Seq(Exists, Sp, K(), Colon, Sp, Naturals(), Comma, Sp,
                And(Positive(K()), Equal(N(), Subtract(Power(D(2), K()), D(1))))))))));
    private static Formula PublishedRing() => F.Id("R");
    private static Formula PublishedSeries() => Call("PowerSeries", PublishedRing());
    private static Formula PublishedBinders() => Seq(Bound("R", Named("Type")),
        OpenBracket, Call("CommRing", PublishedRing()), CloseBracket, Sp);
    private static Formula PublishedAgreeFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), g = F.Id("g"), n = F.Id("n");
        return Disp(Seq(PublishedBinders(), Bound("d", Naturals()),
            Bound("f", PublishedSeries()), Bound("g", PublishedSeries()),
            Equal(Call("Agree", d, f, g), Parenthesized(Seq(Bound("n", Naturals()),
                Implication(Seq(n, Sp, Lt, Sp, d), Equal(Call("coeff", n, f), Call("coeff", n, g))))))));
    }
    private static Formula PublishedPowerFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), g = F.Id("g"), k = F.Id("k");
        return Disp(Seq(PublishedBinders(), Bound("d", Naturals()),
            Bound("f", PublishedSeries()), Bound("g", PublishedSeries()),
            Implication(Call("Agree", d, f, g), Seq(Bound("k", Naturals()),
                Call("Agree", d, Power(f, k), Power(g, k))))));
    }
    private static Formula PublishedProductFormula()
    {
        Formula d = F.Id("d"), f = F.Id("f"), g = F.Id("g"), u = F.Id("u"), v = F.Id("v");
        return Disp(Seq(PublishedBinders(), Bound("d", Naturals()),
            Bound("f", PublishedSeries()), Bound("g", PublishedSeries()),
            Bound("u", PublishedSeries()), Bound("v", PublishedSeries()),
            Implication(Call("Agree", d, f, g), Implication(Call("Agree", d, u, v),
                Call("Agree", d, Mul(f, u), Mul(g, v))))));
    }

    private static Formula PublishedInnerAgreementFormula()
    {
        Formula d = F.Id("d"), u = F.Id("u"), v = F.Id("v"), f = F.Id("f");
        return Disp(Seq(PublishedBinders(), Bound("d", Naturals()),
            Bound("u", PublishedSeries()), Bound("v", PublishedSeries()),
            Implication(Call("Agree", d, u, v), Parenthesized(Seq(Bound("f", PublishedSeries()),
                Implication(Equal(Call("constantCoeff", u), D(0)),
                    Implication(Equal(Call("constantCoeff", v), D(0)),
                        Call("Agree", d, Call("subst", u, f), Call("subst", v, f)))))))));
    }

    private static Formula PublishedConstantFormula()
    {
        Formula f = F.Id("f"), u = F.Id("u");
        return Disp(Seq(PublishedBinders(), Bound("f", PublishedSeries()), Bound("u", PublishedSeries()),
            Implication(Equal(Call("constantCoeff", u), D(0)),
                Equal(Call("constantCoeff", Call("subst", u, f)), Call("constantCoeff", f)))));
    }

    private static Formula PubAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula PubImp(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula PubSubst(Formula f) =>
        new Formula.Apply(Seq(f, Dot, Named("subst")), [Power(X(), D(2))]);
    private static Formula PublishedSquareSubstitution()
    {
        var f = F.Id("f");
        return Disp(PubAll("f", Call("PowerSeries", Call("ZMod", D(2))),
            Equal(Power(f, D(2)), PubSubst(f))));
    }
    private static Formula PublishedLacunaryCoefficients()
    {
        var f = F.Id("f");
        var n = F.Id("n");
        var k = F.Id("k");
        return Disp(PubAll("f", Call("PowerSeries", Call("ZMod", D(2))),
            PubImp(Equal(Call("constantCoeff", f), D(0)),
            PubImp(Equal(Call("coeff", D(1), f), D(1)),
            PubImp(Equal(f, Add(X(), Mul(X(), PubSubst(f)))),
            PubAll("n", Naturals(), Seq(Parenthesized(Equal(Call("coeff", n, f), D(1))), Sp, Iff, Sp,
                Parenthesized(Seq(Exists, Sp, k, Colon, Sp, Naturals(), Comma, Sp,
                    And(Positive(k), Equal(n, Subtract(Power(D(2), k), D(1)))))))))))));
    }
}
