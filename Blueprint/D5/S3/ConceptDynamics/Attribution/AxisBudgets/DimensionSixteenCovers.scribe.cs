using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class AxisBudgetDimensionSixteenCoversDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteenCovers.";
    private static Formula Budget => F.Id("b");
    private static Formula AtEachBudget(Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create("b"),
            new Formula.NamedConstant(FormulaIdentifier.Create("Nat")), body);

    private static Formula CoverExistence()
    {
        Formula edges = F.Id("f");
        Formula mode = F.Id("s");
        Formula conditions = new Formula.Logic(
            Call("CoverSupport", edges),
            FormulaLogicOperator.And,
            new Formula.Logic(
                Call("CoverDegrees", edges, mode),
                FormulaLogicOperator.And,
                new Formula.Relation(Call("AxisCost", edges),
                    FormulaRelationOperator.LessThanOrEqual, Budget)));
        return new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("f"),
            Call("BinaryEdgeTables", D(1,5)),
            new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("s"),
                new Formula.NamedConstant(FormulaIdentifier.Create("Bool")), conditions));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bound the fixed-seed costs of full inclusion and inclusion covers in dimension sixteen.",
        H("Rank bounds for a sixteen-coordinate fixed-seed budget"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sixteen-cover-factor"),
                DeclarationHandle.Create(Prefix + "coverWithin"),
                H("A feasible factor supported on diagonals and inclusion covers"),
                StatementSource.FromAuthor(Disp(AtEachBudget(new Formula.Logic(
                    Call("CoverWithin", Budget), FormulaLogicOperator.Iff,
                    CoverExistence())))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix coordinate zero in dimension sixteen and multiplier three. "
                    + "BinaryEdgeTables(15) is the set of Boolean edge tables on two copies of the "
                    + "subsets of the other fifteen coordinates. CoverSupport(f) excludes the edge "
                    + "from the full set to itself. Any positive entry outside the full-set row must "
                    + "be diagonal or add exactly one element. CoverDegrees(f,s) requires each "
                    + "ordinary row and column to have odd degree at most three. Both full-set "
                    + "vertices have even degree at most two if s is true, and odd degree at most "
                    + "one if s is false. AxisCost(f) is four times the sum of one and the number "
                    + "of selected edges from ordinary odd-rank rows to odd-rank columns."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sixteen-cover-budget-lower"),
                DeclarationHandle.Create(Prefix + "cover_budget_ge"),
                H("Every factor on diagonals and inclusion covers requires at least 2044"),
                StatementSource.FromAuthor(Disp(AtEachBudget(new Formula.Logic(
                    Call("CoverWithin", Budget), FormulaLogicOperator.Implies,
                    new Formula.Relation(D(2,0,4,4), FormulaRelationOperator.LessThanOrEqual, Budget))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If at most one exceptional edge enters the first four layers, "
                    + "the first and third ranks each pay an additional diagonal unit. If two enter, "
                    + "the odd cardinalities and the rank-cut parity at ranks five, seven and nine "
                    + "force three additional diagonal units. Thus at least 510 ordinary edges are "
                    + "charged. The marked column contributes one unit."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sixteen-full-budget-lower"),
                DeclarationHandle.Create(Prefix + "full_budget_ge"),
                H("Full inclusion requires at least 2036 fixed seeds"),
                StatementSource.FromAuthor(Disp(AtEachBudget(new Formula.Logic(
                    Call("AxisFactorWithin", D(3), D(0), Budget), FormulaLogicOperator.Implies,
                    new Formula.Relation(D(2,0,3,6), FormulaRelationOperator.LessThanOrEqual, Budget))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The low-side deficits at ranks one and three and the "
                    + "high-side deficits at ranks eleven and thirteen force 508 charged ordinary "
                    + "edges. The marked edge accounts for one more unit and a unit is four "
                    + "fixed seeds."))),
                DescribeRole.Theorem))));
}
