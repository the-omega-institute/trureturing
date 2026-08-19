using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.OrderTwoBoundary;

internal sealed class GoldenExceptionalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var phi = new Formula.Phi();
        var zero = Num(0);

        Formula Numerator() =>
            Subtract(Subtract(new Formula.Power(phi, Num(2)), phi), Num(1));

        var vanishes = Equal(Numerator(), zero);
        var formulaZero = Equal(Call("championValue", phi), zero);
        var thresholdPos = new Formula.Relation(
            zero, FormulaRelationOperator.LessThan, Id("goldenThreshold"));
        var disagree = new Formula.Relation(
            Call("championValue", phi), FormulaRelationOperator.NotEqual,
            Id("goldenThreshold"));

        var combined = new Formula.Logic(
            new Formula.Logic(vanishes, FormulaLogicOperator.And, formulaZero),
            FormulaLogicOperator.And,
            new Formula.Logic(thresholdPos, FormulaLogicOperator.And, disagree));

        const string declarationPrefix =
            "D5/S0/Tower/OrderTwoBoundary/GoldenExceptional.";

        return DocumentDefinition.Create(ScribeNode.Create(
            "The general champion formula vanishes at order two, so order two lies outside "
                + "its range rather than inside it by a small margin.",
            H("Golden Exceptional"),
            Blocks(
                Paragraph(Text(
                    "The general champion value divides the golden minimal polynomial by the "
                        + "squared base less one. At the golden ratio that numerator is exactly "
                        + "zero, so the formula returns zero while the order-two tower's own "
                        + "champion value is strictly positive. The exclusion of order two from "
                        + "the general statement is therefore structural, not a rounding "
                        + "concession.")),
                Describe.Lean(
                    DescribeId.Create("order-two-lies-outside-the-general-champion-formula"),
                    DeclarationHandle.Create(
                        declarationPrefix + "order_two_is_outside_the_general_formula"),
                    H("Order two lies outside the general formula"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(combined)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The same vanishing numerator also makes the finite-depth argument "
                            + "degenerate at order two: the constraint that the predecessor "
                            + "coordinate stay at or below the reciprocal base reads as "
                            + "positivity of that numerator, and at the golden ratio it holds "
                            + "with equality rather than strictly."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(GidRef.Create(
                    "D5/S0/Tower/DBonacciGeneral/ChampionValue")),
            ]));
    }
}
