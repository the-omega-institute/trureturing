using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class FiniteOrderNegativeCertificateDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Zeros/FiniteOrderNegativeCertificate."
            + "exists_finite_order_negative_certificate";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero weighted positive-order sum has a negative coefficient and a sharp witness.",
        H("Finite-Order Negative Certificate"),
        Blocks(Describe.Lean(
            DescribeId.Create("a-zero-weighted-sum-has-a-negative-finite-order-certificate"),
            DeclarationHandle.Create(Declaration),
            H("A zero weighted sum has a negative finite-order certificate"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let J be a real coefficient family on positive integer orders and let "
                        + "w be strictly positive there. If the weighted family is summable, "
                        + "its sum is zero, and at least one coefficient is nonzero, then some "
                        + "finite order m >= 1 has J(m) < 0.")),
                Paragraph(Text(
                    "The source derives coefficient nontriviality from a nonzero entire "
                        + "function. That analytic carrier and its series identity are absent "
                        + "from the atom, so the formal statement exposes the exact "
                        + "nontriviality premise needed by the series argument.")),
                Paragraph(Text(
                    "Pinned Mathlib's Summable.tsum_pos proves the contradiction: if every "
                        + "coefficient were nonnegative, a nonzero coefficient and a positive "
                        + "weight would make the zero total strictly positive.")),
                Paragraph(Text(
                    "A companion Lean theorem witnesses sharpness with unit weights, "
                        + "J(1) = -1, J(2) = 1, and all remaining coefficients zero. Thus the "
                        + "hypotheses and exact zero-sum boundary are jointly inhabited."))),
            DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TheoremFormula()
    {
        Formula natural = Call("Nat");
        Formula real = Call("Real");
        Formula m = F.Id("m");
        Formula j = F.Id("J");
        Formula w = F.Id("w");
        Formula assumptions = All(
            Call("positiveWeights", w),
            Call("summablePositiveOrders", w, j),
            Equal(Call("weightedSumPositiveOrders", w, j), D(0)),
            Call("nontrivialPositiveOrders", j));
        Formula conclusion = Exists(
            "m",
            natural,
            All(LessEqual(D(1), m), Less(Call("apply", j, m), D(0))));

        return Disp(ForAll(
            [
                Bound("J", new Formula.TypeArrow(natural, real)),
                Bound("w", new Formula.TypeArrow(natural, real)),
            ],
            Implies(assumptions, conclusion)));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(string variable, Formula domain, Formula body) =>
        new Formula.BindMany(
            FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(variable), domain)],
            body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = new Formula.Logic(clauses[index], FormulaLogicOperator.And, result);
        return result;
    }
}
