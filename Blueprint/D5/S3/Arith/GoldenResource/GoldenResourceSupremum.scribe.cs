using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenResourceSupremumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenResourceSupremum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At positive prices the resource supremum equals the finite sum of positive layer gains.",
        H("Golden Resource Supremum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-prime-local-original-layer-sum"),
                DeclarationHandle.Create(Prefix + "local_eq_layer_sum"),
                H("Original prime-local telescoping identity"),
                StatementSource.FromAuthor(LocalLayerSumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original generic private proof is exposed in place for "
                    + "ActualReservePrimeMask. For every real price, actual prime and natural exponent, "
                    + "the local objective is the sum over k in Icc 1 a of log p times "
                    + "(goldenLayerMarginal p k - lambda). Exponent zero gives an empty sum. "
                    + "This visibility change preserves the original statement and proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-objective-at-optimal-positive-part-sum"),
                DeclarationHandle.Create(Prefix + "objective_at_optimal_eq_positive_part_sum"),
                H("The objective at the minimal-count configuration"),
                StatementSource.FromAuthor(OptimalValueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive price and a positive integer realizing optimalLayerCount "
                        + "at every natural p, the objective equals the sum of log p times "
                        + "the net marginal over all strictly profitable prime-layer pairs. "
                        + "The frozen count specification supplies such an integer. The proof "
                        + "telescopes the public single-layer delta along each prime power, "
                        + "then regroups the finite active-pair set by prime. This is the "
                        + "value identity used by the supremum theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-supremum-positive-part-sum"),
                DeclarationHandle.Create(Prefix + "golden_resource_supremum_eq_positive_part_sum"),
                H("The exact unconstrained optimal value"),
                StatementSource.FromAuthor(SupremumFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The supremum ranges over objective values of all positive integers. "
                            + "The frozen count specification supplies a greatest element, "
                            + "so this supremum is attained and equals the objective evaluated "
                            + "in the preceding theorem.")),
                    Paragraph(Text(
                        "The sum is indexed by the finite set of all pairs (p,k) with p prime, "
                            + "k at least one, and marginal strictly above lambda. Thus each "
                            + "included net marginal equals its positive part; all excluded "
                            + "positive-index prime layers have zero positive part. This finite "
                            + "support presentation expresses the positive-part double sum. "
                            + "The hypothesis lambda greater than zero is essential. No claim "
                            + "about nonpositive prices or the RH boundary is made.")),
                    Paragraph(Text(
                        "A finite prime mask gives a useful actual-reserve application of these "
                            + "existing results. Fix a real x > 1 and set lambda_x = 1/(x log x). "
                            + "For a prime p let v_p(x) = max {k : p^k <= x}; this cutoff is inclusive. "
                            + "Write u_p(a) = log(sum from k=0 to a of p^(-k)) - lambda_x a log p, "
                            + "Q_p(a) = sum from k=1 to a of 1/(k p^k), and "
                            + "H_p(a) = Q_p(a) - lambda_x a log p. Define the complete finite "
                            + "reference F(x) = sum over primes p <= x of H_p(v_p(x)), "
                            + "J_x(n) = log(sigma(n)/n) - lambda_x log n for every n >= 1, "
                            + "and Psi(x) = sup over all n >= 1 of J_x(n). "
                            + "For a finite set S of primes put "
                            + "D(S) = sum over p in S of [1/p - log(1+1/p)] and "
                            + "L(S) = sum over p in S of 1/[2p(p+1)].")),
                    Paragraph(Text(
                        "Assume p+1 <= x and 2x <= p^2 for every p in S. The first-layer "
                            + "price condition follows from lambda_x log p <= 1/x <= 1/(p+1) "
                            + "<= log(1+1/p). For the next layer, GoldenLayerMarginalDecay gives "
                            + "marginal(p,2) <= p^(-2)/log p <= lambda_x: indeed "
                            + "log x <= 2 log p and 2x <= p^2 imply x log x <= p^2 log p. "
                            + "GoldenLocalThreshold then gives u_p(a) <= u_p(1) for every "
                            + "natural exponent a. The same mask conditions give v_p(x)=1. "
                            + "Thus H_p(v_p(x))-u_p(a) >= 1/p-log(1+1/p). "
                            + "PrefixDeficitKernel.result at a=1 and z=1/p gives "
                            + "1/[2p(p+1)] <= 1/p-log(1+1/p).")),
                    Paragraph(Text(
                        "The entire complement is retained. ReferencePrefixDominance gives "
                            + "u_p(a) <= H_p(a). The increment of H_p at layer k is "
                            + "1/(k p^k)-lambda_x log p; log monotonicity makes it nonnegative "
                            + "for p^k <= x and nonpositive above that inclusive cutoff. "
                            + "Consequently H_p(a) <= H_p(v_p(x)) for every prime and exponent. "
                            + "For any positive integer n, sum on the finite union of its prime "
                            + "support with the reference primes p <= x. Reference terms outside "
                            + "that reference set vanish because v_p(x)=0 there. "
                            + "GoldenResourceObjectiveFactorization identifies the actual sum "
                            + "with J_x(n), and every complementary prime contributes "
                            + "nonnegatively. This yields D(S) <= F(x)-J_x(n) for all n >= 1, "
                            + "without any assumption that the prime support of n is contained in S.")),
                    Paragraph(Text(
                        "The positive price lambda_x has an attained unrestricted optimizer by "
                            + "GoldenResourceOptimalLayerCount. Applying the preceding bound at "
                            + "that optimizer gives L(S) <= D(S) <= R(x), where "
                            + "R(x)=F(x)-Psi(x). For every positive integer the remaining "
                            + "optimizer deficit d_n(x)=Psi(x)-J_x(n) is nonnegative, and "
                            + "F(x)-J_x(n)=R(x)+d_n(x). This application pays an explicit "
                            + "actual reserve using the project's 5040 objective machinery; "
                            + "it is a combined application of existing results. "
                            + "In a Robin explicit-formula argument at x=log n, the signed "
                            + "condition I_psi(x)+R(x)+d_n(x)>0 is still required. "
                            + "The mask estimate controls neither the sign nor the size of "
                            + "I_psi, and does not justify dropping d_n. It proves no new "
                            + "Robin counterexample floor or full Riemann hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-equality-price-invariance"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_eq_of_layer_price"),
                H("Equality-price layers preserve the objective"),
                StatementSource.FromAuthor(EqualityPriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every real price, positive integer n and prime p, if the next p-layer "
                        + "has marginal equal to the price, n and n times p have equal "
                        + "objectives. Reading the equality in reverse also describes removal "
                        + "of that layer. This companion is a direct application of the frozen "
                        + "single-layer delta to the equality-price clause."))),
                DescribeRole.Theorem))));

    private static Formula LocalLayerSumFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula k = F.Id("k");
        Formula sum = Seq(Sum, Underscore,
            Grp(Seq(k, InMacro, Sp, Call("Icc", D(1), a))), Sp,
            Product(Call("log", p), Seq(Open, Subtract(Marginal(p, k), lambda), Close)));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("p", Naturals()), Bound("a", Naturals())],
            Implies(Call("Prime", p),
                Equal(Call("goldenPrimeLocalObjective", lambda, p, a), sum))));
    }

    private static Formula ActiveSum(Formula lambda)
    {
        Formula p = F.Id("p");
        Formula k = F.Id("k");
        Formula pair = Seq(Open, p, Comma, k, Close);
        Formula active = SetBuilder(pair, Seq(Naturals(), Times, Naturals()),
            And(Le(D(1), k), And(Call("Prime", p), Lt(lambda, Marginal(p, k)))));
        return Seq(Sum, Underscore, Grp(Seq(pair, InMacro, active)), Sp,
            Product(Call("log", p), Seq(Open, Subtract(Marginal(p, k), lambda), Close)));
    }

    private static Formula OptimalValueFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula counts = ForAll([Bound("p", Naturals())],
            Equal(Call("factorization", n, p), Call("optimalLayerCount", lambda, p)));
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(And(Lt(D(0), lambda), And(Le(D(1), n), counts)),
                Equal(Objective(lambda, n), ActiveSum(lambda)))));
    }

    private static Formula SupremumFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula x = F.Id("x");
        Formula realized = new Formula.BindMany(FormulaQuantifier.Exists,
            [Bound("n", Naturals())], And(Le(D(1), n), Equal(Objective(lambda, n), x)));
        Formula values = SetBuilder(x, Reals(), realized);
        return Disp(ForAll([Bound("lambda", Reals())], Implies(Lt(D(0), lambda),
            Equal(Call("sSup", values), ActiveSum(lambda)))));
    }

    private static Formula EqualityPriceFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula price = Equal(Marginal(p, Add(Call("factorization", n, p), D(1))), lambda);
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals()), Bound("p", Naturals())],
            Implies(And(Le(D(1), n), And(Call("Prime", p), price)),
                Equal(Objective(lambda, Product(n, p)), Objective(lambda, n)))));
    }

    private static Formula SetBuilder(Formula variable, Formula domain, Formula predicate) =>
        Seq(OpenBrace, variable, Colon, Sp, domain, Sp, Mid, Sp, predicate, CloseBrace);
    private static Formula Objective(Formula lambda, Formula n) =>
        Call("goldenResourceObjective", lambda, n);
    private static Formula Marginal(Formula p, Formula k) => Call("goldenLayerMarginal", p, k);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
