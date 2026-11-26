using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedSupportDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var dimension = F.Id("n");
        var multiplier = F.Id("k");
        var budget = F.Id("z");
        var hypotheses = new Formula.Logic(
            Call("Even", Seq(dimension, Sp, Plus, Sp, D(2))),
            FormulaLogicOperator.And,
            Call("Odd", multiplier));
        var equivalence = new Formula.Logic(
            Call("SeedCountsWithin", dimension, multiplier, budget),
            FormulaLogicOperator.Iff,
            Call("MarkedParitySupportWithin", dimension, multiplier, budget));
        return Disp(new Formula.Logic(
            Seq(Open, hypotheses, Close), FormulaLogicOperator.Implies,
            Seq(Open, equivalence, Close)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Characterize simultaneous coordinate bounds by a parity support with one marked column.",
        H("A marked parity support for coordinate budgets"),
        Blocks(Describe.Lean(
            DescribeId.Create("marked-parity-support-coordinate-budgets"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParitySeedSupport.binary_support_iff"),
            H("Coordinate budgets at odd multiplier"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The dimension is n plus two. Its even parity gives a full row. "
                    + "The odd multiplier forces a column with two odd colour masses in that row. "
                    + "Rows are even subsets and columns are odd subsets of the coordinates. "
                    + "For each coordinate the budget bounds its fixed-seed count on the same "
                    + "uniform equivariant seed action.")),
                Paragraph(Text("Choose a binary table and a marked column of the full row. "
                    + "When the marked cell has binary value zero, give it base mass two. "
                    + "All other base masses are their binary values. Each row and column "
                    + "must have odd base mass at most the multiplier.")),
                Paragraph(Text("At each coordinate, count ordinary odd cells whose two profiles "
                    + "contain it, and count the marked column once if it contains that coordinate. "
                    + "Four times this count must fit the corresponding budget.")),
                Paragraph(Text("Complete the remaining margins with even masses, using the "
                    + "residual row and column margins. Split the full row "
                    + "between its two colours with odd mass only at the marked column. In the "
                    + "reverse direction, a given realization supplies the marked column "
                    + "and a binary support whose counts fit all budgets."))),
            DescribeRole.Theorem))));
}
