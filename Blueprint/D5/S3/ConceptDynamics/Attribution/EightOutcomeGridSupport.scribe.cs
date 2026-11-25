using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class EightOutcomeGridSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact seed support for the denominator 210 grid on eight labels.",
        H("Three regular orbits are necessary and sufficient"),
        Blocks(Describe.Lean(
            DescribeId.Create("eight-outcome-denominator-two-hundred-ten"),
            DeclarationHandle.Create(
                "D5/S3/ConceptDynamics/Attribution/EightOutcomeGridSupport.grid_support_budget_iff"),
            H("Exact seed budget for eight labels and denominator 210"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "SeedBudget(k,m,B) means there is a finite seed set of cardinality at most B "
                    + "with an action of all permutations of the k labels. The invariant real seed "
                    + "weights are positive and sum to one. A single deterministic equivariant "
                    + "readout reproduces each coordinate divided by m for every natural profile "
                    + "of total m.")),
                Paragraph(Text(
                    "The primes at most eight divide 210, so the prime-cycle profile test forces "
                    + "regular seed orbits. A tied-coordinate profile can prescribe every integer "
                    + "from zero to thirty in denominator units. In each regular orbit eight "
                    + "stabilizer blocks supply a digit between zero and eight for a tied label. "
                    + "At least two orbits are required by the number of distinct digit vectors. "
                    + "For two orbits their scaled weights sum to fifteen quarters by normalization. "
                    + "The code bound for integer masses on two-digit diagonals leaves only "
                    + "twenty-seven codes, fewer than the thirty-one required levels.")),
                Paragraph(Text(
                    "The complete-grid theorem gives three orbits at denominator 1680. Multiplying "
                    + "each input coordinate by eight embeds the coarser profiles in that grid. "
                    + "This embedding commutes with label permutations and preserves every "
                    + "coordinate divided by its denominator."))),
            DescribeRole.Theorem))));

    private static Formula Statement()
    {
        Formula budget = F.Id("B");
        Formula law = new Formula.FunctionCall(FormulaIdentifier.Create("SeedBudget"),
            [D(8), D(2, 1, 0), budget]);
        return Disp(Seq(Forall, Sp, budget, Comma, Sp, law, Sp, Iff, Sp,
            D(1, 2, 0, 9, 6, 0), Sp, Le, Sp, budget));
    }
}
