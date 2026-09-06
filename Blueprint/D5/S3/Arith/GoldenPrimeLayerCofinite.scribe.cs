using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenPrimeLayerCofiniteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenPrimeLayerCofinite.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At every positive price, all positive layer marginals lie below the price beyond "
            + "one uniform prime cutoff.",
        H("Golden Prime Layer Cofiniteness"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-prime-layer-uniform-cutoff"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_lt_of_prime_le"),
                H("Only finitely many primes can support a profitable layer"),
                StatementSource.FromAuthor(UniformPrimeCutoffFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every positive real price lambda, there is a natural cutoff P "
                            + "such that every prime p at least P and every positive layer a "
                            + "have marginal benefit strictly below lambda.")),
                    Paragraph(Text(
                        "The proof first shows that 1/p divided by log p tends to zero as p "
                            + "grows. It then consumes the frozen geometric marginal bound "
                            + "and the inequality (1/p)^a at most 1/p for every positive a. "
                            + "This controls the prime half of the atom's finiteness claim; "
                            + "the fixed-prime exponent half is carried by the preceding "
                            + "marginal-decay module."))),
                DescribeRole.Theorem))));

    private static Formula UniformPrimeCutoffFormula()
    {
        Formula lambda = F.Id("lambda");
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula cutoff = F.Id("P");
        Formula assumptions = And(
            Call("Prime", p),
            And(Le(cutoff, p), Le(D(1), a)));
        Formula tail = ForAll(
            [Bound("p", Naturals()), Bound("a", Naturals())],
            Implies(
                assumptions,
                Lt(Call("goldenLayerMarginal", p, a), lambda)));
        Formula existsCutoff = ExistsMany([Bound("P", Naturals())], tail);
        return Disp(ForAll(
            [Bound("lambda", Reals())],
            Implies(Lt(D(0), lambda), existsCutoff)));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
}
