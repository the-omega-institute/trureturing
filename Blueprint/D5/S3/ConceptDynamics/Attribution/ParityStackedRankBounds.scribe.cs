using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParityStackedRankBoundsDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var ranks = F.Id("R");
        var mass = F.Id("m");
        var flags = F.Id("b");
        var score = Call("IntersectionCount", n, mass, flags);
        return Disp(new Formula.Logic(
            Call("OddUniformMargins", n, k, ranks, mass, flags), FormulaLogicOperator.Implies,
            Seq(Call("RankDeficits", n, k, ranks), Sp, Le, Sp, score)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous rank deficits for an odd-margin parity table.",
        H("Add high even rank deficits for one common table"),
        Blocks(Describe.Lean(
            DescribeId.Create("stacked-odd-parity-rank-deficits"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParityStackedRankBounds.stacked_fixed_from_odd_margins"),
            H("Rank deficits under odd uniform margins"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The dimension n is even and at least six. Each row and column "
                    + "of the natural-number table has odd marginal k. Each chosen threshold r "
                    + "lies between 4 and n minus 2, inclusive. At least one column has a "
                    + "positive full-row flag bounded by the corresponding full-row mass.")),
                Paragraph(Text("Each ordinary cell contributes its mass modulo two times the "
                    + "size of the intersection of the row and column. Each cell in the full "
                    + "row uses its flag instead.")),
                Paragraph(Text("The lower bound starts with one and adds the positive part of "
                    + "the number of weight-(n minus 1) odd columns plus one minus 2k. For "
                    + "each threshold r it also adds the positive part of one plus the number "
                    + "of ordinary even rows of weight at least r minus k times the number "
                    + "of odd columns of weight at most n minus r.")),
                Paragraph(Text("A cell can satisfy several cut shortages. Distinct cut "
                    + "thresholds occupy distinct places in an integer interval of size at "
                    + "most the size of the cell's intersection. A positive full-row flag "
                    + "pays for the thresholds above the rank range of its column."))),
            DescribeRole.Theorem))));
}
