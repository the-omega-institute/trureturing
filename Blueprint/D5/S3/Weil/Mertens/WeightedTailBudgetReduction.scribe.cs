using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens;

internal sealed class WeightedTailBudgetReductionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Weil/Mertens/WeightedTailBudgetReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite reduction of the weighted Robin budget",
        H("The sign needed for forward transport"),
        Blocks(
            Describe.Lean(DescribeId.Create("finite-weighted-budget-bounds"),
                DeclarationHandle.Create(Module + "budget_bounds"),
                H("Two-sided comparison with an explicit endpoint error"),
                StatementSource.FromAuthor(Bounds()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix 2 ≤ Y ≤ B ≤ C and 0 < κ ≤ 1/2. For a real kernel "
                        + "integrable on (Y, ∞), let Q be the ordinary tail, J the logarithmically "
                        + "weighted tail, a the inverse logarithmic weight, and E=Q−aJ. "
                        + "Assume the negative part of Q at u is at most u^(κ−1/2) on [Y,C].")),
                    Paragraph(Text("W is the integral of a(t) times the negative part of J(t) "
                        + "against dt/sqrt(t), plus sqrt(Y) times the negative part of E(B). "
                        + "Let F(t) be the signed density tail at C plus the integral from t to C "
                        + "of the positive part of Q against the negative derivative of the weight. "
                        + "Form Wred using the positive part of a(t)F(t)−max(Q(t),0) in the integral "
                        + "and the negative part of a(B)F(B) at the endpoint.")),
                    Paragraph(Text("The omitted negative tail is nonnegative and, after normalizing "
                        + "by a(t), is at most t^(κ−1/2). Subtracting it from the already bounded "
                        + "negative part of Q gives the pointwise error. Taking positive parts "
                        + "preserves the bound, whose integral is M=(B^κ−Y^κ)/κ. The endpoint "
                        + "contribution increases by at most sqrt(Y) B^(κ−1/2)."))),
                DescribeRole.Theorem))));

    private static Formula Bounds()
    {
        var w = F.Id("W");
        var reduced = F.Id("Wred");
        var m = F.Id("M");
        var exponent = Subtract(F.Id("kappa"), new Formula.Fraction(D(1), D(2)));
        var endpoint = Multiply(new Formula.FunctionCall(FormulaIdentifier.Create("sqrt"), [F.Id("Y")]),
            Seq(F.Id("B"), Caret, Grp(exponent)));
        return Disp(new Formula.Logic(
            new Formula.Relation(Subtract(reduced, m), FormulaRelationOperator.LessThanOrEqual, w),
            FormulaLogicOperator.And,
            new Formula.Relation(w, FormulaRelationOperator.LessThanOrEqual,
                Add(Add(reduced, m), endpoint))));
    }
}
