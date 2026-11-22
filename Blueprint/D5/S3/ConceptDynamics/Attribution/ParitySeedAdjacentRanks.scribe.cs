using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;


namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedAdjacentRanksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Attribution/ParitySeedAdjacentRanks.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refute adjacent-rank compression at an eight-coordinate fixed-seed budget of 36.",
        H("A fixed-seed budget that requires an edge skipping a rank"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("adjacent-rank-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The adjacent-rank assertion at budget 36"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(
                    Call("AxisFactorWithin", D(3), D(0), D(36)),
                    FormulaLogicOperator.Implies,
                    Call("AdjacentAxisFactorWithin", D(3), D(0), D(36))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix coordinate zero in dimension eight and multiplier three. The assertion "
                    + "says that a factor within budget 36 still exists when each ordinary allowed "
                    + "edge either joins two copies of the same subset or adds exactly one element. "
                    + "The exceptional row of the full subset keeps all its outgoing edges except "
                    + "the deleted marked edge. The two full-subset vertices use the same choice "
                    + "of parity and cap, namely even degrees at most two or odd degrees at most "
                    + "one. All other degrees are odd and at most three. The cost is four times "
                    + "one plus the number of ordinary chosen edges joining two odd subsets."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("adjacent-rank-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The adjacent-rank assertion is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The explicit unrestricted factor has score at most 36. The kernel checks "
                        + "the row and column degrees, inclusion on ordinary edges, the absent "
                        + "marked edge and the total cost.")),
                    Paragraph(Text(
                        "Under the adjacent-rank restriction, ordinary paid edges are diagonal. "
                        + "Columns of ranks zero and one force at least three paid edges in rank "
                        + "one. Rows of ranks five and six and the capacity of columns of ranks six "
                        + "and seven force at least five paid edges in rank five. With at most eight "
                        + "paid edges, there can be no rank-three diagonal and the full-subset row "
                        + "must send two edges into ranks zero and one, using all its capacity.")),
                    Paragraph(Text(
                        "The 35 odd-degree rows of rank three now force an odd number of edges "
                        + "from rank three to four. Equal parity of the row and column degree sums "
                        + "through rank three makes that number even, since the only edges entering "
                        + "those columns from above are the two edges from the full-subset row. "
                        + "The contradiction forces at least nine paid edges and hence cost 40 "
                        + "or more under the restriction."))),
                DescribeRole.Theorem))));
}
