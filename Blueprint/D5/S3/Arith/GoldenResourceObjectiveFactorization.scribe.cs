using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenResourceObjectiveFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenResourceObjectiveFactorization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every real resource price, the objective of a positive integer is the finite sum "
            + "of its prime-direction local objectives.",
        H("Golden Resource Objective Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-resource-objective-factorization"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_factorization"),
                H("The objective factors over prime directions"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real price lambda and positive natural number n, the global "
                            + "resource objective equals the sum over the prime factors of n of "
                            + "the local objective at the corresponding factorization exponent. "
                            + "The proof applies Mathlib's multiplicative factorization of sigma, "
                            + "the logarithm of a finite product, and the prime-power geometric "
                            + "sum formula.")),
                    Paragraph(Text(
                        "This is the cross-prime version of the atom's displayed local identity. "
                            + "It does not compute the unrestricted optimum, characterize optimal "
                            + "exponents, prove finiteness of profitable layers, settle tied "
                            + "thresholds, or address the boundary at 5040."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-resource-objective-sum-on"),
                DeclarationHandle.Create(Prefix + "golden_resource_objective_sum_on"),
                H("The objective sums over any finite prime superset"),
                StatementSource.FromAuthor(SumOnFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a finite set s contains every prime factor of a positive n, the same "
                        + "objective is the sum of the local objectives over s. Exponents outside "
                        + "the prime support are zero and their local terms vanish. This companion "
                        + "result consumes the factorization theorem, so the dependency direction "
                        + "is sum_on to factorization."))),
                DescribeRole.Theorem))));

    private static Formula FactorizationFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula support = Call("primeFactors", n);
        Formula exponent = Call("factorization", n, p);
        Formula summand = Call("goldenPrimeLocalObjective", lambda, p, exponent);
        Formula sum = Seq(
            new Formula.Subscript(Sum,
                Relation(p, FormulaRelationOperator.MemberOf, support)),
            Sp, summand);
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals())],
            Implies(Le(D(1), n),
                Equal(Call("goldenResourceObjective", lambda, n), sum))));
    }

    private static Formula SumOnFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("n");
        Formula p = F.Id("p");
        Formula s = F.Id("s");
        Formula support = Call("primeFactors", n);
        Formula exponent = Call("factorization", n, p);
        Formula summand = Call("goldenPrimeLocalObjective", lambda, p, exponent);
        Formula sum = Seq(
            new Formula.Subscript(Sum,
                Relation(p, FormulaRelationOperator.MemberOf, s)),
            Sp, summand);
        Formula assumptions = And(
            Le(D(1), n),
            Relation(support, FormulaRelationOperator.SubsetOf, s));
        return Disp(ForAll(
            [Bound("lambda", Reals()), Bound("n", Naturals()),
                Bound("s", Call("Finset", Naturals()))],
            Implies(assumptions,
                Equal(Call("goldenResourceObjective", lambda, n), sum))));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
