using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.AllOrder;

internal sealed class WeightedMonomialDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/AllOrder/WeightedMonomial.AdmissibleWeight."
            + "admissible_weight_ordered_sublevel_spec";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An admissible additive weight canonically lists every finite nonzero "
            + "monomial sublevel in strict weight order.",
        H("Weighted Monomial Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("admissible-weight-ordered-sublevel-spec"),
            DeclarationHandle.Create(Declaration),
            H("Admissible weights give compatible finite elimination orders"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "This theorem supplies the canonical finite monomial order for the "
                        + "golden Euler germ extraction ladder of OACTC parts 580 and 581.")),
                Paragraph(Text(
                    "Admissibility makes each strict sublevel finite. Injectivity of the "
                        + "weight turns sorting by nondecreasing weight into a strict order, "
                        + "while positivity removes exactly the zero monomial.")),
                Paragraph(Text(
                    "Threshold enlargement preserves the earlier list as an initial segment. "
                        + "This advances the finite ordering boundary, but it does not construct "
                        + "Euler factors or a weighted ledger, prove cancellation, uniqueness, "
                        + "or ledger nestedness, complete all-order extraction, or establish "
                        + "O-5 or RH."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator relation,
        Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula monomial = Call("GoldenMonomial");
        Formula real = Call("Real");
        Formula weight = F.Id("w");
        Formula threshold = F.Id("T");
        Formula largerThreshold = F.Id("Tp");
        Formula list = F.Id("l");
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula orderedSublevel = Call("increasingWeightSublevel", weight, threshold);

        Formula membership = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", monomial)],
            Iff(
                Relation(m, FormulaRelationOperator.MemberOf, list),
                And(
                    Relation(m, FormulaRelationOperator.NotEqual, D(0)),
                    Relation(Call("w", m), FormulaRelationOperator.LessThan, threshold))));
        Formula weightComparison = Relation(
            Call("w", m),
            FormulaRelationOperator.LessThan,
            Call("w", n));
        Formula positiveWeights = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("m", monomial)],
            Implies(
                Relation(m, FormulaRelationOperator.MemberOf, list),
                Relation(D(0), FormulaRelationOperator.LessThan, Call("w", m))));
        Formula strictOrder = Call(
            "Pairwise",
            list,
            Seq(Open, m, Comma, Sp, n, Sp, Mapsto, Sp, weightComparison, Close));
        Formula prefixCompatibility = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("Tp", real)],
            Implies(
                Relation(threshold, FormulaRelationOperator.LessThanOrEqual, largerThreshold),
                Call(
                    "IsPrefix",
                    list,
                    Call("increasingWeightSublevel", weight, largerThreshold))));
        Formula conclusion = And(
            Call("Nodup", list),
            And(membership, And(positiveWeights, And(strictOrder, prefixCompatibility))));

        return Disp(new Formula.Aligned([
            Seq(Call("AdmissibleWeight", weight), Comma, Sp,
                list, Sp, Colon, Eq, Sp, orderedSublevel, Comma),
            conclusion,
        ]));
    }
}
