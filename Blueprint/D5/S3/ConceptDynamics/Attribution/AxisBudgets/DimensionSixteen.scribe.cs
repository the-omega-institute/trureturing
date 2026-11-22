using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution.AxisBudgets;

internal sealed class AxisBudgetDimensionSixteenDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/AxisBudgets/DimensionSixteen.";
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
        "Compare full inclusion and inclusion covers in the one-coordinate Boolean lattice.",
        H("A sixteen-coordinate budget that requires an edge skipping ranks"),
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
                DescribeId.Create("sixteen-full-budget-iff"),
                DeclarationHandle.Create(Prefix + "full_budget_iff"),
                H("The full inclusion graph has minimum budget 2036"),
                StatementSource.FromAuthor(Disp(AtEachBudget(new Formula.Logic(
                    Call("AxisFactorWithin", D(3), D(0), Budget), FormulaLogicOperator.Iff,
                    new Formula.Relation(D(2,0,3,6), FormulaRelationOperator.LessThanOrEqual, Budget))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The rank-capacity inequality charges at least 11, 211, 213 and 73 "
                    + "ordinary edges at ranks one, three, eleven and thirteen. The marked contribution "
                    + "raises the normalized cost from 508 to 509. A checked binary factor attains this "
                    + "bound. Its only ordinary edge spanning multiple ranks goes from the first four "
                    + "available coordinates to the first ten."))),
                DescribeRole.Theorem),
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
                DescribeId.Create("sixteen-cover-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The adjacent-rank assertion at budget 2036"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    Call("AxisFactorWithin", D(3), D(0), D(2,0,3,6)), FormulaLogicOperator.Implies,
                    Call("CoverWithin", D(2,0,3,6))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The assertion says that feasibility at budget 2036 in the full "
                    + "inclusion graph entails feasibility on diagonals and inclusion covers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sixteen-cover-refutation"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The adjacent-rank assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full graph has a feasible factor at budget 2036. A cover "
                    + "factor with this budget would give the incompatible inequalities "
                    + "2044 at most the budget and the budget at most 2036."))),
                DescribeRole.Theorem))));
}
