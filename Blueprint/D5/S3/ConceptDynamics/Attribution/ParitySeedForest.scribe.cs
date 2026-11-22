using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedForestDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var dimensionOffset = F.Id("n");
        var multiplier = F.Id("k");
        var budget = F.Id("z");
        var hypotheses = new Formula.Logic(
            Call("Even", Seq(dimensionOffset, Sp, Plus, Sp, D(2))),
            FormulaLogicOperator.And,
            Call("Odd", multiplier));
        var equivalence = new Formula.Logic(
            Call("SeedCountsWithin", dimensionOffset, multiplier, budget),
            FormulaLogicOperator.Iff,
            Call("MarkedForestWithin", dimensionOffset, multiplier, budget));
        return Disp(new Formula.Logic(
            Seq(Open, hypotheses, Close), FormulaLogicOperator.Implies,
            Seq(Open, equivalence, Close)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reduce simultaneous coordinate budgets to an acyclic marked parity support.",
        H("Forests suffice for marked parity support"),
        Blocks(Describe.Lean(
            DescribeId.Create("marked-parity-forest-coordinate-budgets"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParitySeedForest.forest_support_iff"),
            H("Coordinate budgets via a forest"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("In dimension n plus two, the seed side asks for one equivariant "
                    + "uniform seed action with every coordinate fixed count bounded by its "
                    + "corresponding budget. The forest side uses the marked binary support and "
                    + "base margins from the marked support criterion. It also requires the "
                    + "graph of the selected binary entries to be acyclic.")),
                Paragraph(Text("Delete the edges of a cycle. Every affected row or column loses "
                    + "two selected cells. If the cycle uses the marked cell, its base mass "
                    + "changes from one to two. The net base mass at each of its endpoints "
                    + "keeps its previous value. Other affected margins decrease by two.")),
                Paragraph(Text("The marked column contributes just as before, and each ordinary "
                    + "coordinate contribution can only decrease. A feasible subtable with "
                    + "the fewest selected cells is therefore acyclic. Every marked forest "
                    + "supplies a seed action by the binary criterion."))),
            DescribeRole.Theorem))));
}
