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
                    Call("ExistsCoverFactor", Budget))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix coordinate zero in dimension sixteen and multiplier three. "
                    + "The two vertex sets are copies of the subsets of the other fifteen coordinates. "
                    + "A positive ordinary entry must be diagonal or add one element. The exceptional "
                    + "full-set row can use every target except the full set. Both full-set vertices have "
                    + "even degree at most two in the selected mode, or odd degree at most one in the "
                    + "other mode. All ordinary degrees are odd and at most three. The budget bounds "
                    + "four times one plus the number of selected ordinary edges with two odd endpoints."))),
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
