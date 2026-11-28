using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class SchulteLiouvilleCubeMobiusDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/SchulteLiouvilleCubeMobius.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/schulte2018a299406");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Schulte's A299406 coefficients equal the Liouville function times A210826.",
        H("Schulte's Liouville and Cube-Mobius Identity"),
        Blocks(
            Paragraph(Text("N denotes the natural numbers including zero, Z the integers, and "
                + "ArithmeticFunction(Z) the integer-valued functions on N that vanish at zero. "
                + "The indices n and k are natural numbers, and f is such an arithmetic function. "
                + "The arithmetic function zeta is one on positive inputs and zero at zero; "
                + "mu is the Mobius function; intCast(zeta) is its integer-valued cast, the "
                + "coercion from ArithmeticFunction(N) to ArithmeticFunction(Z) that the "
                + "convolutions with the integer-valued mu require. Omega counts prime "
                + "factors with multiplicity, and "
                + "lambda denotes Mathlib's liouville, A008836: at a positive index it is minus "
                + "one raised to Omega of that index. A and B denote A299406 and A210826. "
                + "The binary star is Dirichlet convolution, while the centered dot is integer "
                + "multiplication of values. Nat.floorRoot divides each prime-factor exponent "
                + "by k using natural-number division and returns zero when k or n is zero; "
                + "it is the root for the divisibility order. The function liftPow keeps the "
                + "value of f at this root exactly when its k-th power equals n. For positive k, "
                + "its Dirichlet series is obtained by replacing the series variable s by k*s. "
                + "Reading the Dirichlet generating function coefficientwise sends zeta(6s) "
                + "to liftPow(6,zeta) and the reciprocals of zeta(2s) and zeta(3s) to "
                + "liftPow(2,mu) and liftPow(3,mu). In the Lambert series, x is a formal "
                + "variable: the sum of B(d) over positive divisors d of n equals the cube "
                + "indicator, so Mobius inversion gives B as mu convolved with that indicator. "
                + "Only the A299406 formula a(n) = A008836(n) * A210826(n) is asserted here, "
                + "under these coefficient readings. Analytic convergence and other OEIS "
                + "assertions are outside the claim. The positive-index hypothesis follows "
                + "the offset one of A299406.")),
            Node("liftPow", "The exact power lift", LiftFormula(),
                "The two defining clauses retain f at the factorization root on exact powers "
                + "and give zero otherwise. They also describe the total definition when k is "
                + "zero; the coefficient interpretation uses only positive k. Each displayed "
                + "zero in a value equality is an integer.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("A", "The A299406 coefficient function", AFormula(),
                "The four convolution factors encode zeta(s) zeta(6s) divided by "
                + "zeta(2s) zeta(3s). The zeta factors here are integer-valued, matching "
                + "the natural-to-integer coercions in the Lean definition.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("B", "The Lambert-series coefficient function", BFormula(),
                "The function liftPow(3,zeta) is one on positive cubes and zero elsewhere. "
                + "Convolution with mu inverts the positive-divisor sum in the Lambert "
                + "series defining A210826.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("liftPow_apply_pow", "Coefficients at exact powers", PowerLiftAtPower(),
                "At an exact positive-degree power, the lift evaluates the original function at the base.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("liftPow_apply_nonpow", "Coefficients outside exact powers", PowerLiftOutsidePowers(),
                "If the input has no natural k-th root, its coefficient in the lift is zero.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("liftPow_isMultiplicative", "Multiplicativity of the power lift", PowerLiftMultiplicative(),
                "Coprime factors of an exact power are exact powers of the same degree.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("liftPow_prime_pow", "Power lift on prime powers", PowerLiftOnPrimePowers(),
                "The exponent must be divisible by the lift degree. The quotient is natural-number division.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("conv_prime_pow", "Convolution on prime powers", ConvolutionOnPrimePowers(),
                "The divisors of p raised to e have exponents from zero to e. Their complementary exponents use natural subtraction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lift_moebius_prime_pow", "Lifted Möbius function on prime powers", MoebiusLiftOnPrimePowers(),
                "The two integer indicators give one at exponent zero and minus one at exponent k.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("lift_zeta_prime_pow", "Lifted zeta on prime powers", ZetaLiftOnPrimePowers(),
                "The integer-valued lift gives one exactly when k divides the exponent.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo()),
            Node("result", "Schulte's product formula", ResultFormula(),
                "Every convolution factor is multiplicative. On a prime power with exponent "
                + "e, both sides have values 1, 1, 0, -1, -1, 0 as e runs through the six "
                + "residue classes. Equality on all prime powers therefore gives equality "
                + "at every positive natural index.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a299406-schulte-liouville-cube-mobius"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? claim = null) =>
        Describe.Lean(DescribeId.Create("a299406-" + name.ToLowerInvariant().Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula IntZeta() => Call(Named("intCast"), Named(Zeta));
    private static Formula Named(Formula symbol) => Seq(Operatorname, Grp(symbol));
    private static Formula Call(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Convolve(Formula left, Formula right) => Seq(left, Sp, Star, Sp, right);
    private static Formula Bound(Formula variable, Formula domain) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp);
    private static Formula Implication(Formula hypothesis, Formula conclusion) =>
        Seq(Parenthesized(hypothesis), Sp, Implies, Sp, Parenthesized(conclusion));

    private static Formula LiftFormula()
    {
        Formula k = F.Id("k"), f = F.Id("f"), n = F.Id("n");
        Formula root = Call(Named("floorRoot"), k, n);
        Formula power = new Formula.Power(root, k);
        Formula value = Call(Call(Named("liftPow"), k, f), n);
        Formula exact = Implication(Equal(power, n), Equal(value, Call(f, root)));
        Formula other = Implication(Seq(power, Sp, Neq, Sp, n), Equal(value, D(0)));
        return Disp(Seq(Bound(k, Naturals()), Bound(f, Call(Named("ArithmeticFunction"), Integers())),
            Bound(n, Naturals()), Parenthesized(exact), Sp, Land, Sp, Parenthesized(other)));
    }

    private static Formula AFormula() => Disp(Equal(Named("A"),
        Convolve(Parenthesized(Convolve(Parenthesized(Convolve(IntZeta(),
            Call(Named("liftPow"), D(6), IntZeta()))),
            Call(Named("liftPow"), D(2), Named(Mu)))),
            Call(Named("liftPow"), D(3), Named(Mu)))));

    private static Formula BFormula() => Disp(Equal(Named("B"),
        Convolve(Named(Mu), Call(Named("liftPow"), D(3), IntZeta()))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ArithmeticFunctions() => Call(Named("ArithmeticFunction"), Integers());
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Pow(Formula basis, Formula exponent) => new Formula.Power(basis, exponent);
    private static Formula Lift(Formula k, Formula f) => Call(Named("liftPow"), k, f);
    private static Formula Ne(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);
    private static Formula If(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(F.Id("if"), Sp, Parenthesized(condition), Sp, F.Id("then"), Sp, yes,
            Sp, F.Id("else"), Sp, no));

    private static Formula PowerLiftAtPower()
    {
        Formula k = F.Id("k"), f = F.Id("f"), m = F.Id("m");
        Formula value = Equal(Call(Lift(k, f), Pow(m, k)), Call(f, m));
        Formula coefficients = All("f", ArithmeticFunctions(), All("m", Naturals(), value));
        return Disp(All("k", Naturals(), Implication(Ne(k, D(0)), coefficients)));
    }

    private static Formula PowerLiftOutsidePowers()
    {
        Formula k = F.Id("k"), f = F.Id("f"), n = F.Id("n"), m = F.Id("m");
        Formula root = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("m"),
            Naturals(), Equal(Pow(m, k), n));
        return Disp(All("k", Naturals(), All("f", ArithmeticFunctions(), All("n", Naturals(),
            Implication(Seq(F.Id("Not"), Sp, Parenthesized(root)), Equal(Call(Lift(k, f), n), D(0)))))));
    }

    private static Formula PowerLiftMultiplicative()
    {
        Formula k = F.Id("k"), f = F.Id("f");
        Formula multiplicative = Qualified("ArithmeticFunction", "IsMultiplicative");
        return Disp(All("k", Naturals(), Implication(Ne(k, D(0)), All("f", ArithmeticFunctions(),
            Implication(Call(multiplicative, f), Call(multiplicative, Lift(k, f)))))));
    }

    private static Formula OnPrimePowers(Formula body) =>
        All("p", Naturals(), All("e", Naturals(),
            Implication(Call(Qualified("Nat", "Prime"), F.Id("p")), body)));

    private static Formula PowerLiftOnPrimePowers()
    {
        Formula k = F.Id("k"), f = F.Id("f"), p = F.Id("p"), e = F.Id("e");
        Formula quotient = Call(Qualified("Nat", "div"), e, k);
        Formula value = Equal(Call(Lift(k, f), Pow(p, e)),
            If(Divides(k, e), Call(f, Pow(p, quotient)), D(0)));
        Formula coefficients = All("f", ArithmeticFunctions(), OnPrimePowers(value));
        return Disp(All("k", Naturals(), Implication(Ne(k, D(0)), coefficients)));
    }

    private static Formula ConvolutionOnPrimePowers()
    {
        Formula f = F.Id("f"), g = F.Id("g"), p = F.Id("p"), e = F.Id("e"), i = F.Id("i");
        Formula summand = Multiply(Call(f, Pow(p, i)), Call(g, Pow(p, Subtract(e, i))));
        Formula function = Parenthesized(Seq(F.Id("fun"), Sp, i, Colon, Naturals(), Sp, Mapsto, Sp, summand));
        Formula sum = Call(Qualified("Finset", "sum"), Call(Qualified("Finset", "range"), Add(e, D(1))), function);
        return Disp(All("f", ArithmeticFunctions(), All("g", ArithmeticFunctions(), OnPrimePowers(
            Equal(Call(Parenthesized(Convolve(f, g)), Pow(p, e)), sum)))));
    }

    private static Formula MoebiusLiftOnPrimePowers()
    {
        Formula k = F.Id("k"), p = F.Id("p"), e = F.Id("e");
        Formula difference = Subtract(If(Equal(e, D(0)), D(1), D(0)), If(Equal(e, k), D(1), D(0)));
        Formula value = Equal(Call(Lift(k, Named(Mu)), Pow(p, e)), difference);
        return Disp(All("k", Naturals(), Implication(Ne(k, D(0)), OnPrimePowers(value))));
    }

    private static Formula ZetaLiftOnPrimePowers()
    {
        Formula k = F.Id("k"), p = F.Id("p"), e = F.Id("e");
        Formula zeta = Call(Qualified("ArithmeticFunction", "natCoe"), Qualified("ArithmeticFunction", "zeta"));
        Formula value = Equal(Call(Lift(k, zeta), Pow(p, e)), If(Divides(k, e), D(1), D(0)));
        return Disp(All("k", Naturals(), Implication(Ne(k, D(0)), OnPrimePowers(value))));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        return Disp(Seq(Bound(n, Naturals()),
            Implication(Seq(D(0), Sp, Lt, Sp, n),
                Equal(Call(Named("A"), n), new Formula.Binary(Call(Named(LambdaLower), n),
                    FormulaBinaryOperator.Multiply, Call(Named("B"), n))))));
    }
}
