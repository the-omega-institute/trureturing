using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class ParitySeedAxisFactorDocument : IScribeDocumentDefinition
{
    private static Formula Statement()
    {
        var dimensionOffset = F.Id("n");
        var multiplier = F.Id("k");
        var coordinate = F.Id("i");
        var budget = F.Id("b");
        var hypotheses = new Formula.Logic(
            Call("Even", Seq(dimensionOffset, Sp, Plus, Sp, D(2))),
            FormulaLogicOperator.And,
            Call("Odd", multiplier));
        var equivalence = new Formula.Logic(
            Call("SeedCountsOnAxisWithin", dimensionOffset, multiplier, coordinate, budget),
            FormulaLogicOperator.Iff,
            Call("AxisFactorWithin", dimensionOffset, multiplier, coordinate, budget));
        return Disp(new Formula.Logic(
            Seq(Open, hypotheses, Close), FormulaLogicOperator.Implies,
            Seq(Open, equivalence, Close)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Characterize single-coordinate fixed-seed budgets by subset inclusion and parity.",
        H("Single-coordinate budgets on the Boolean lattice"),
        Blocks(Describe.Lean(
            DescribeId.Create("single-coordinate-budget-boolean-lattice-factor"),
            DeclarationHandle.Create("D5/S3/ConceptDynamics/Attribution/ParitySeedAxisFactor.axis_budget_iff"),
            H("A Boolean lattice factor for a single-coordinate budget"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The seed side in dimension n plus two requires zero fixed seeds "
                    + "outside the specified coordinate i and at most b on that coordinate. Both "
                    + "marginals are uniform on their opposite-parity slices.")),
                Paragraph(Text("The graph side uses two copies of the subsets of all coordinates "
                    + "except i. Denote the full subset by T. An edge from A to B is allowed when "
                    + "A is contained in B or A equals T. The edge from T to T is excluded. "
                    + "Choose either even degrees at most k minus one at both copies of T, or odd "
                    + "degrees at most k minus two there with k at least three. Other vertices "
                    + "have odd degree at most k.")),
                Paragraph(Text("The score is four times the sum of one and the number of chosen edges from "
                    + "an odd subset other than T to an odd subset. Its upper bound is b.")),
                Paragraph(Text("Zero counts outside i force the mark to be the singleton of i and "
                    + "every ordinary selected profile pair to intersect only within that singleton. "
                    + "Delete i from the row profile and from the complement of the column profile. "
                    + "The parities recover the deleted bits, and the zero-count constraint becomes "
                    + "subset inclusion. The two marked endpoints both become T."))),
            DescribeRole.Theorem))));
}
