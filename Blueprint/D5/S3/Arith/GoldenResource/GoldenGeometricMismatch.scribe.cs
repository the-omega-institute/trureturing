using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class GoldenGeometricMismatchDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResource/GoldenGeometricMismatch.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite geometric mismatch bounds for the actual divisor-benefit objective.",
        H("Geometric prime-exponent mismatch"),
        Blocks(
            Paragraph(Text(
                "The pressure objective, its prime-direction contributions, and classical benefit "
                + "are inherited objects. The existing Nicolas-benefit library note records the "
                + "strict one-over-p separation argument and the half-price cost beyond the first "
                + "extra layer. Neither is claimed as new research. The formal increment reuses "
                + "goldenPrimeLocalObjective and the original single-layer difference proof in "
                + "GoldenLocalThreshold; the finite global comparison reuses the original "
                + "objective factorization and minimal-count optimizer.")),
            Paragraph(Text(
                "Write beta(p,k)=log(p)*goldenLayerMarginal(p,k) and t=lambda*log(p) in this "
                + "exposition. For a<m the budget is beta(p,m)*sum(i<m-a,p^i)-t*(m-a); "
                + "for m<a it is t*(a-m)-beta(p,m+1)*sum(i<a-m,p^(-i)); for a=m it is zero. "
                + "The missing-layer branch has m at least one. At distance one both branches "
                + "retain the exact price slack. The contraction is a consumed helper; "
                + "the accumulated, unbounded actual-objective estimate is the formal contribution.")),
            Describe.Lean(
                DescribeId.Create("golden-geometric-mismatch-local-gap"),
                DeclarationHandle.Create(Prefix + "prime_power_objective_gap_ge_geometric_mismatch"),
                H("Both geometric sums bound the actual local gap"),
                StatementSource.FromAuthor(LocalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prime p, real price lambda and natural exponents a,m, "
                    + "the budget is at most the actual local objective at m minus that at a. "
                    + "This comparison does not require threshold or positive-price hypotheses. "
                    + "Missing layers are accumulated backwards with powers of p; excess "
                    + "layers are accumulated forwards with powers of its inverse. "
                    + "No unrelated objective or trial integer is substituted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-geometric-mismatch-coercive"),
                DeclarationHandle.Create(Prefix + "geometric_mismatch_budget_coercive"),
                H("Two thresholds give nonnegative quantitative payment"),
                StatementSource.FromAuthor(CoerciveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a positive price, assume lambda at most the marginal at m when m>0, "
                    + "and the next marginal at most lambda. The budget is nonnegative and "
                    + "at least lambda*log(p)/2 times max(|a-m|-1,0). "
                    + "The conclusion includes both equality-price endpoints. It permits "
                    + "zero payment, and does not assert a strictly positive deficit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-geometric-mismatch-actual-support"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_gap_ge_geometric_mismatch"),
                H("Keep every mismatch of the actual integer"),
                StatementSource.FromAuthor(GlobalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For positive n and M, with every exponent of M equal to the existing "
                        + "optimalLayerCount at the same positive lambda, sum on the finite union "
                        + "of their actual prime supports. The summed budget lies between the "
                        + "weighted distance bound and goldenResourceObjective(lambda,M) minus "
                        + "goldenResourceObjective(lambda,n), and is nonnegative. It also bounds "
                        + "the actual pressure deficit: the supremum over all positive integers "
                        + "minus the actual objective at n, using the frozen supremum identity. "
                        + "The existing optimal_layer_count_spec supplies M. No exponent "
                        + "mismatch is omitted and no infinite Summable claim is used.")),
                    Paragraph(Text(
                        "The full RH/Robin/FIB obligation remains Ipsi(log n)+R(log n)+d_n>0 "
                        + "for every n>5040. This estimate alone does not pay the signed low part, "
                        + "original unit, common prime-power cutoff, or both odd-prefix clipping "
                        + "boundaries. The proposed joint sufficient inequality and the advisory "
                        + "zero-deficit claim at 720720 are unverified here. Escape registration "
                        + "has a faithful local-objective family attempt, but exact source binding "
                        + "and the other targets remain unfinished under issue5214; "
                        + "no declared_validated status is asserted."))),
                DescribeRole.Theorem))));

    private static Formula LocalFormula()
    {
        Formula l = F.Id("lambda"), p = F.Id("p"), a = F.Id("a"), m = F.Id("m");
        return Disp(ForAll([Bound("lambda", Reals()), Bound("p", Naturals()),
            Bound("a", Naturals()), Bound("m", Naturals())],
            Implies(Call("Prime", p), Le(Budget(l, p, a, m),
                Sub(Local(l, p, m), Local(l, p, a))))));
    }

    private static Formula CoerciveFormula()
    {
        Formula l = F.Id("lambda"), p = F.Id("p"), a = F.Id("a"), m = F.Id("m");
        Formula lower = Implies(Lt(D(0), m), Le(l, Call("goldenLayerMarginal", p, m)));
        Formula upper = Le(Call("goldenLayerMarginal", p, Add(m, D(1))), l);
        Formula cost = Mul(Div(Mul(l, Call("log", p)), D(2)), TailDistance(a, m));
        return Disp(ForAll([Bound("lambda", Reals()), Bound("p", Naturals()),
            Bound("a", Naturals()), Bound("m", Naturals())],
            Implies(And(Call("Prime", p), And(Lt(D(0), l), And(lower, upper))),
                And(Le(cost, Budget(l, p, a, m)), Le(D(0), Budget(l, p, a, m))))));
    }

    private static Formula GlobalFormula()
    {
        Formula l = F.Id("lambda"), n = F.Id("n"), m = F.Id("M"), p = F.Id("p");
        Formula counts = ForAll([Bound("p", Naturals())],
            Eq(Call("factorization", m, p), Call("optimalLayerCount", l, p)));
        Formula support = Call("union", Call("primeFactors", n), Call("primeFactors", m));
        Formula an = Call("factorization", n, p), am = Call("factorization", m, p);
        Formula budgets = FiniteSum(p, support, Budget(l, p, an, am));
        Formula coarse = Mul(Div(l, D(2)), FiniteSum(p, support,
            Mul(Call("log", p), TailDistance(an, am))));
        Formula x = F.Id("x"), nn = F.Id("N");
        Formula values = Seq(OpenBrace, x, Sp, Mid, Sp,
            new Formula.BindMany(FormulaQuantifier.Exists, [Bound("N", Naturals())],
                And(Le(D(1), nn), Eq(Call("goldenResourceObjective", l, nn), x))), CloseBrace);
        return Disp(ForAll([Bound("lambda", Reals()), Bound("n", Naturals()),
            Bound("M", Naturals())],
            Implies(And(Lt(D(0), l), And(Le(D(1), n), And(Le(D(1), m), counts))),
                And(Le(coarse, budgets), And(Le(budgets,
                    Sub(Call("goldenResourceObjective", l, m),
                        Call("goldenResourceObjective", l, n))), And(Le(D(0), budgets),
                        Le(budgets, Sub(Call("sSup", values),
                            Call("goldenResourceObjective", l, n)))))))));
    }

    private static Formula Budget(Formula l, Formula p, Formula a, Formula m) =>
        Call("geometricMismatchBudget", l, p, a, m);
    private static Formula Local(Formula l, Formula p, Formula a) =>
        Call("goldenPrimeLocalObjective", l, p, a);
    private static Formula TailDistance(Formula a, Formula m) =>
        Call("max", Sub(Call("abs", Sub(a, m)), D(1)), D(0));
    private static Formula FiniteSum(Formula p, Formula s, Formula f) =>
        Seq(Sum, Underscore, Grp(Seq(p, InMacro, s)), Sp, f);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
    private static Formula ForAll(Formula.BoundVariable[] vars, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. vars], body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
