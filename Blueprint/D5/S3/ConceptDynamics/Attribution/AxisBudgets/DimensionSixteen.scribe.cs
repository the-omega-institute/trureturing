using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class AxisBudgetDimensionSixteenDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound a multiplier-three single-coordinate budget in dimension sixteen.",
        H("A single-coordinate budget lower bound in dimension sixteen"),
        Blocks(Describe.Lean(
            DescribeId.Create("dimension-sixteen-axis-budget-lower-bound"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.axis_budget_ge_2036"),
            H("Every feasible one-coordinate budget is at least 2036"),
            StatementSource.FromAuthor(Disp(new Formula.Logic(
                Call("AxisFactorWithin", D(3), F.Id("i"), F.Id("b")), FormulaLogicOperator.Implies,
                new Formula.Relation(D(2036), FormulaRelationOperator.LessThanOrEqual, F.Id("b"))))),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let i be any coordinate of a sixteen-element set and let b be a natural "
                    + "number. Use the Boolean lattice criterion at multiplier three. The graph is on "
                    + "two copies of the subsets of the other fifteen coordinates. Ordinary edges "
                    + "follow inclusion, and the full-set row may send edges to non-full columns. "
                    + "The feasible budget b includes four times one plus the number of ordinary edges "
                    + "whose endpoints both have odd rank.")),
                Paragraph(Text("Assign signed weights to the left and right ranks. On every allowed "
                    + "edge their sum is at most the edge charge. The positive weights use the lower "
                    + "bounds on degrees. The negative weights use the upper bounds of three on "
                    + "ordinary vertices and two on the full-set vertices. Binomial layer sizes give "
                    + "lower and upper rank contributions of 222 and 286 charged edges. The two contributions "
                    + "give a budget lower bound of 4 times 509."))),
            DescribeRole.Theorem))));
}
