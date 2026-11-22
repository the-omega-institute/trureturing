using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedFactorDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var dimensionOffset = F.Id("n");
        var multiplier = F.Id("k");
        var budget = F.Id("b");
        var hypotheses = new Formula.Logic(
            Call("Even", Seq(dimensionOffset, Sp, Plus, Sp, D(2))),
            FormulaLogicOperator.And,
            Call("Odd", multiplier));
        var equivalence = new Formula.Logic(
            Call("SeedCountsWithin", dimensionOffset, multiplier, budget),
            FormulaLogicOperator.Iff,
            Call("MarkedFactorWithin", dimensionOffset, multiplier, budget));
        return Disp(new Formula.Logic(
            Seq(Open, hypotheses, Close), FormulaLogicOperator.Implies,
            Seq(Open, equivalence, Close)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Express simultaneous coordinate budgets through degree constraints and additive edge counts.",
        H("Parity factors for coordinate budgets"),
        Blocks(Describe.Lean(
            DescribeId.Create("marked-parity-factor-coordinate-budgets"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParitySeedFactor.parity_factor_budget_iff"),
            H("Coordinate budgets via a parity factor"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In dimension n plus two, the seed side asks for one equivariant uniform "
                    + "seed action with every coordinate fixed count bounded by its budget b.")),
                Paragraph(Text("The factor side chooses a marked odd column and a Boolean indicating "
                    + "whether the marked cell was selected. The residual bipartite support excludes "
                    + "the edge between the all-ones row and that column. When the bit is true, "
                    + "both endpoints have even degree at most k minus one. When it is false, k "
                    + "is at least three and both endpoints have odd degree at most k minus two. "
                    + "Every other vertex has odd degree at most k.")),
                Paragraph(Text("For each coordinate, the count is four times the sum of the marked-column "
                    + "membership indicator and the number of residual edges whose row is other than "
                    + "the all-ones row and whose two endpoints both contain the coordinate. Each "
                    + "count must be at most the corresponding budget.")),
                Paragraph(Text("Remove the marked edge and retain its bit. In each affected margin, "
                    + "the original base mass equals the residual degree plus one for a true bit "
                    + "or plus two for a false bit. Restoring the bit reverses this construction. "
                    + "Both operations preserve the coordinate counts of the marked support."))),
            DescribeRole.Theorem))));
}
