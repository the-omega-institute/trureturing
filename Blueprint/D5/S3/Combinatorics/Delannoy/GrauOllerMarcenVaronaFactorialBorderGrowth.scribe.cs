using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Delannoy;

internal sealed class GrauOllerMarcenVaronaFactorialBorderGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Delannoy/GrauOllerMarcenVaronaFactorialBorderGrowth.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/grauollermarcenvarona2022delannoy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The factorial-border Delannoy diagonal ratio differs from n + 1 by a quantity tending to zero.",
        H("The factorial-border Delannoy conjecture"),
        Blocks(
            Node("f", "The bordered Delannoy array", ArrayFormula(),
                "The source array satisfies f_{m,n} = α f_{m−1,n} + β f_{m,n−1} + γ f_{m−1,n−1}, with prescribed borders. "
                    + "Section 6, arXiv page 18: \"This happens, for instance, if α = β = γ = 1 and f_{n,0} = f_{0,n} = n!.\" "
                    + "Here b is any natural border, both axes use b, and the origin has value b(0). The three displayed equations give every recursion case.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claimFactorial", "The additive-error factorial-border limit",
                new Formula.Logic(F.Id("claimFactorial"), FormulaLogicOperator.Iff, ClaimBody()),
                "Section 6, arXiv page 18: \"In this example [19, OEIS A346374] we conjecture that f_{n+1,n+1}/f_{n,n} ≈ n + 1 (where a_n ≈ b_n means, as usual, that a_n − b_n → 0 when n → ∞).\" "
                    + "The border is Nat.factorial, including 0! = 1. The diagonal entries and n are cast to the reals, and the ratio uses real division.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Definition("delta", "Border increments", DeltaFormula(),
                "The first increment is b(0); every later increment is the real difference of consecutive border values."),
            Definition("conv", "The finite border convolution", ConvolutionFormula(),
                "The sum includes j = 0 through m. The second factor is the unit-border array. The index m−j uses natural subtraction."),
            Theorem("diagonal_convolution", "The exact diagonal convolution", DiagonalFormula(),
                "Induction in the two coordinates gives the full border convolution; its two symmetric terms agree on the diagonal."),
            Definition("W", "The limiting factorial weights", WeightFormula("W", 2),
                "The positive exponential-series weights are 2^k/k!."),
            Definition("M", "A summable majorant", WeightFormula("M", 6),
                "The weights 6^k/k! bound the entire normalized convolution, including indices past n."),
            Definition("Q", "The normalized unit-border kernel", QFormula(),
                "For k ≤ n the numerator is the polynomial qAB(k,n) evaluated at one, the binomial sum for the unit-border Delannoy array. For k > n the kernel is zero."),
            Theorem("Q_of_gt", "The kernel vanishes past n", AllN("n", AllN("k",
                Implies(Less(N(), K()), Equal(Call("Q", N(), K()), D(0))))),
                "The zero branch gives finite support in k."),
            Theorem("Q_nonneg", "The kernel is nonnegative", AllN("n", AllN("k",
                AtMost(D(0), Call("Q", N(), K())))),
                "Every binomial summand and denominator is nonnegative."),
            Theorem("W_le_M", "The majorant bounds the limiting weights", AllN("k",
                AtMost(Call("W", K()), Call("M", K()))),
                "The inequality follows from 2^k ≤ 6^k and the positive factorial denominator."),
            Theorem("Q_scaled_bound", "A global first-order bound", AllN("n", AllN("k",
                AtMost(new Formula.Absolute(Multiply(Cast(N()), Subtract(Call("Q", N(), K()), Call("W", K())))),
                    Multiply(Cast(K()), Call("M", K()))))),
                "The lower-degree terms in the binomial kernel are bounded by k times the majorant, uniformly in n. The zero extension obeys the same bound."),
            Definition("G", "The fixed-index first-order coefficient", GFormula(),
                "The finite sum has at most one nonzero term, namely i = k − 1 when k is positive."),
            Theorem("Q_scaled_limit", "The fixed-index first-order limit", AllN("k",
                Tendsto(LambdaN("n", Multiply(Cast(N()), Subtract(Call("Q", N(), K()), Call("W", K())))), Call("G", K()))),
                "The asymptotic formula for Nat.choose reduces each fixed-index quotient to a power of 1/n; only the immediately lower degree survives scaling by n."),
            Theorem("summable_M", "The majorant is summable", Apply(Named("Summable"), F.Id("M")),
                "This is the summability of the exponential series at six."),
            Theorem("summable_succ_M", "The linearly weighted majorant is summable",
                Apply(Named("Summable"), Parenthesized(LambdaN("k", Multiply(Add(Cast(K()), D(1)), Call("M", K()))))),
                "The additional polynomial factor is bounded by an exponential weight."),
            Theorem("tendsto_of_scaled", "First-order convergence implies convergence", ScaledConvergenceFormula(),
                "Multiplying the scaled error by 1/n gives convergence of the unscaled error to zero."),
            Definition("P", "The preceding-border correction", PFormula(),
                "For k < n divide Q(n,k) by the real cast of the natural number n−k. Otherwise the correction is zero."),
            Theorem("P_scaled_bound", "The correction has a summable bound", AllN("n", AllN("k",
                AtMost(new Formula.Absolute(Multiply(Cast(N()), Call("P", N(), K()))),
                    Multiply(Add(Cast(K()), D(1)), Call("M", K()))))),
                "The elementary inequality n ≤ (k+1)(n−k) bounds the additional factor on the nonzero branch."),
            Theorem("P_scaled_limit", "The fixed-index correction limit", AllN("k",
                Tendsto(LambdaN("n", Multiply(Cast(N()), Call("P", N(), K()))), Call("W", K()))),
                "For fixed k, n/(n−k) tends to one and Q(n,k) tends to W(k)."),
            Theorem("diagonal_Q_scaled_limit", "The diagonal kernel is negligible",
                Tendsto(LambdaN("n", Multiply(Cast(N()), Call("Q", N(), N()))), D(0)),
                "The diagonal term is squeezed by n M(n), which tends to zero by summability."),
            Theorem("Q_factorial", "The factorial form of the kernel", FactorialKernelFormula(),
                "The factorial identity for Nat.choose converts the denominator to the normalized factorial border."),
            Theorem("ratio_transfer", "First-order ratio transfer", RatioTransferFormula(),
                "A first-order expansion of r gives (n+1)(r(n+1)−r(n)) → 0. If a = b r with a nonzero limiting r, the diagonal and border ratios differ by a quantity tending to zero."),
            Node("result", "The factorial-border limit holds", ClaimBody(),
                "The exact convolution splits the normalized diagonal into Q, P and its diagonal correction. "
                    + "Their global summable bounds permit first-order dominated convergence. "
                    + "The limiting normalizing constant is positive because W(0) = 1. "
                    + "First-order ratio transfer then gives the stated additive-error limit. "
                    + "No explicit rate or second-order expansion is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Definition(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Definition, AssessedProvenance.FromRepo());
    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Node(name, title, formula, prose, DescribeRole.Theorem, AssessedProvenance.FromRepo());
    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
        DescribeId.Create("gv-factorial-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
        provenance, Blocks(Paragraph(Text(prose))), role);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Apply(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N() => F.Id("n");
    private static Formula K() => F.Id("k");
    private static Formula Cast(Formula value) => Parenthesized(Seq(value, Sp, Colon, Sp, Reals()));
    private static Formula CastNat(Formula value) => Cast(Parenthesized(Seq(value, Sp, Colon, Sp, Naturals())));
    private static Formula Arrow(Formula left, Formula right) => new Formula.TypeArrow(left, right);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula AllN(string name, Formula body) => All(name, Naturals(), body);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula AtMost(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LambdaN(string name, Formula body) => Seq(Named("fun"), Sp,
        Parenthesized(Seq(F.Id(name), Colon, Naturals())), Sp, Mapsto, Sp, body);
    private static Formula Tendsto(Formula function, Formula limit) => Apply(Qualified("Filter", "Tendsto"),
        Parenthesized(function), Qualified("Filter", "atTop"), Parenthesized(Seq(Mathcal, Grp(F.Id("N")), Parenthesized(limit))));
    private static Formula If(Formula condition, Formula yes, Formula no) => Seq(Named("if"), Sp,
        Parenthesized(condition), Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Factorial(Formula n) => Apply(Qualified("Nat", "factorial"), n);
    private static Formula Choose(Formula n, Formula k) => Apply(Qualified("Nat", "choose"), n, k);
    private static Formula FiniteSum(string name, Formula length, Formula term) => Seq(
        new Formula.Subscript(F.Sum, Seq(F.Id(name), Sp, InMacro, Sp, Apply(Qualified("Finset", "range"), length))),
        Sp, Parenthesized(term));
    private static Formula UnitArray(Formula m, Formula n) => Cast(Call("f",
        Parenthesized(Seq(Named("fun"), Sp, Parenthesized(Seq(Underscore, Colon, Naturals())), Sp, Mapsto, Sp, D(1))), m, n));

    private static Formula ArrayFormula()
    {
        Formula b = F.Id("b"), m = F.Id("m"), n = N();
        var bt = Arrow(Naturals(), Naturals());
        return new Formula.Aligned([
            All("b", bt, AllN("n", Equal(Call("f", b, D(0), n), Apply(b, n)))),
            All("b", bt, AllN("m", Equal(Call("f", b, Add(m, D(1)), D(0)), Apply(b, Add(m, D(1)))))),
            All("b", bt, AllN("m", AllN("n", Equal(Call("f", b, Add(m, D(1)), Add(n, D(1))),
                Add(Add(Call("f", b, m, Add(n, D(1))), Call("f", b, Add(m, D(1)), n)), Call("f", b, m, n))))))]);
    }
    private static Formula ClaimBody()
    {
        var border = Qualified("Nat", "factorial");
        return Tendsto(LambdaN("n", Subtract(new Formula.Fraction(
            Cast(Call("f", border, Add(N(), D(1)), Add(N(), D(1)))), Cast(Call("f", border, N(), N()))),
            Parenthesized(Add(Cast(N()), D(1))))), D(0));
    }
    private static Formula DeltaFormula()
    {
        Formula b = F.Id("b");
        var bt = Arrow(Naturals(), Naturals());
        return new Formula.Aligned([
            All("b", bt, Equal(Call("delta", b, D(0)), Cast(Apply(b, D(0))))),
            All("b", bt, AllN("n", Equal(Call("delta", b, Add(N(), D(1))),
                Subtract(Cast(Apply(b, Add(N(), D(1)))), Cast(Apply(b, N()))))))]);
    }
    private static Formula ConvolutionFormula()
    {
        Formula a = F.Id("a"), m = F.Id("m"), j = F.Id("j");
        return All("a", Arrow(Naturals(), Reals()), AllN("m", AllN("n", Equal(Call("conv", a, m, N()),
            FiniteSum("j", Add(m, D(1)), Multiply(Apply(a, j), UnitArray(Subtract(m, j), N())))))));
    }
    private static Formula DiagonalFormula()
    {
        Formula b = F.Id("b");
        return All("b", Arrow(Naturals(), Naturals()), AllN("n", Equal(Cast(Call("f", b, N(), N())),
            Subtract(Multiply(D(2), Call("conv", Apply(Named("delta"), b), N(), N())),
                Multiply(Cast(Apply(b, D(0))), UnitArray(N(), N()))))));
    }
    private static Formula WeightFormula(string name, byte value) => AllN("k", Equal(Call(name, K()),
        new Formula.Fraction(new Formula.Power(Cast(D(value)), K()), Cast(Factorial(K())))));
    private static Formula QFormula()
    {
        var numerator = Apply(Qualified("Polynomial", "eval"), D(1), Call("qAB", K(), N()));
        return AllN("n", AllN("k", Equal(Call("Q", N(), K()), If(AtMost(K(), N()),
            new Formula.Fraction(numerator, Multiply(Cast(Factorial(K())), Cast(Choose(N(), K())))), D(0)))));
    }
    private static Formula GFormula()
    {
        Formula i = F.Id("i");
        var weight = Multiply(new Formula.Power(Cast(D(2)), i), Cast(Choose(K(), i)));
        var term = Multiply(weight, If(Equal(K(), Add(i, D(1))), Cast(K()), D(0)));
        var coefficient = Multiply(new Formula.Fraction(D(1), Cast(Factorial(K()))), FiniteSum("i", K(), term));
        return AllN("k", Equal(Call("G", K()), coefficient));
    }
    private static Formula PFormula() => AllN("n", AllN("k", Equal(Call("P", N(), K()),
        If(Less(K(), N()), new Formula.Fraction(Call("Q", N(), K()), CastNat(Subtract(N(), K()))), D(0)))));
    private static Formula FactorialKernelFormula() => AllN("n", AllN("k", Implies(AtMost(K(), N()),
        Equal(Call("Q", N(), K()), new Formula.Fraction(
            Multiply(Cast(Factorial(Subtract(N(), K()))), UnitArray(K(), N())), Cast(Factorial(N())))))));
    private static Formula ScaledConvergenceFormula()
    {
        Formula r = F.Id("r"), c = F.Id("C"), k = F.Id("K");
        return All("r", Arrow(Naturals(), Reals()), All("C", Reals(), All("K", Reals(),
            Implies(Tendsto(LambdaN("n", Multiply(Cast(N()), Subtract(Apply(r, N()), c))), k), Tendsto(r, c)))));
    }
    private static Formula RatioTransferFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), r = F.Id("r"), c = F.Id("C"), k = F.Id("K"), l = F.Id("L");
        var bRatio = new Formula.Fraction(Apply(b, Add(N(), D(1))), Apply(b, N()));
        var positive = AllN("n", NotEqual(Apply(b, N()), D(0)));
        var factorization = AllN("n", Equal(Apply(a, N()), Multiply(Apply(b, N()), Apply(r, N()))));
        var firstOrder = Tendsto(LambdaN("n", Multiply(Cast(N()), Subtract(Apply(r, N()), c))), k);
        var borderRatio = Tendsto(LambdaN("n", new Formula.Fraction(bRatio, Add(Cast(N()), D(1)))), l);
        var conclusion = Tendsto(LambdaN("n", Subtract(
            new Formula.Fraction(Apply(a, Add(N(), D(1))), Apply(a, N())), bRatio)), D(0));
        return All("a", Arrow(Naturals(), Reals()), All("b", Arrow(Naturals(), Reals()),
            All("r", Arrow(Naturals(), Reals()), All("C", Reals(), All("K", Reals(), All("L", Reals(),
                Implies(And(positive, And(factorization, And(NotEqual(c, D(0)), And(Tendsto(r, c), And(firstOrder, borderRatio))))), conclusion)))))));
    }
}
