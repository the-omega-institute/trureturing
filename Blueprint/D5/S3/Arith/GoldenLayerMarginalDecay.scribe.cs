using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class GoldenLayerMarginalDecayDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/GoldenLayerMarginalDecay.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prime-layer marginals have a geometric upper bound and eventually fall below "
            + "every positive price along each fixed prime direction.",
        H("Golden Layer Marginal Decay"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("golden-layer-marginal-geometric-bound"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_le_inv_pow"),
                H("A geometric bound for every positive prime layer"),
                StatementSource.FromAuthor(MarginalBoundFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every prime p and positive layer a, the marginal benefit is at "
                            + "most p to the negative a divided by log p.")),
                    Paragraph(Text(
                        "The proof bounds log x by x minus one for the ratio of consecutive "
                            + "reciprocal geometric factors. Its algebraic core proves that "
                            + "this ratio minus one is at most p to the negative a."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("golden-layer-marginal-eventual-price-bound"),
                DeclarationHandle.Create(Prefix + "golden_layer_marginal_lt_of_le"),
                H("Only finitely many layers exceed a positive price at a fixed prime"),
                StatementSource.FromAuthor(EventualPriceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed prime p and positive real price lambda, there is a "
                            + "natural cutoff N after which every layer marginal is strictly "
                            + "below lambda.")),
                    Paragraph(Text(
                        "The geometric upper bound is consumed together with convergence of "
                            + "the powers of 1/p to zero. This theorem controls exponents at "
                            + "one fixed prime; it does not assert that only finitely many "
                            + "different primes can exceed the price."))),
                DescribeRole.Theorem))));

    private static Formula MarginalBoundFormula()
    {
        Formula p = F.Id("p");
        Formula a = F.Id("a");
        Formula hypotheses = And(Call("Prime", p), Le(D(1), a));
        Formula inversePower = new Formula.Power(
            new Formula.Fraction(D(1), p),
            a);
        Formula conclusion = Le(
            Call("goldenLayerMarginal", p, a),
            new Formula.Fraction(inversePower, Call("log", p)));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("a", Naturals())],
            Implies(hypotheses, conclusion)));
    }

    private static Formula EventualPriceFormula()
    {
        Formula p = F.Id("p");
        Formula lambda = F.Id("lambda");
        Formula n = F.Id("N");
        Formula a = F.Id("a");
        Formula tail = ForAll(
            [Bound("a", Naturals())],
            Implies(
                Le(n, a),
                Lt(Call("goldenLayerMarginal", p, a), lambda)));
        Formula cutoff = ExistsMany([Bound("N", Naturals())], tail);
        Formula hypotheses = And(Call("Prime", p), Lt(D(0), lambda));
        return Disp(ForAll(
            [Bound("p", Naturals()), Bound("lambda", Reals())],
            Implies(hypotheses, cutoff)));
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
