using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class KnownNameSimulationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simulation of a deterministic name-query strategy using only known-name oracle calls.",
        H("Synthetic misses on undisclosed names"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("known-name-simulated-budget"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.simulated_sent_names_bound"),
                H("The simulated strategy preserves the query budget"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take a deterministic strategy whose depth is at most a given budget on "
                    + "every answer branch. Start the simulation with a specified set of known "
                    + "names. Each successful reply adds the queried name and all returned "
                    + "neighbor names. A miss leaves the known set as it was. The simulation "
                    + "asks the oracle only when the queried name is in the current known set "
                    + "and returns a synthetic miss internally on any other name. Its number "
                    + "of oracle calls is at most the original "
                    + "budget because each simulated step follows one answer branch and makes "
                    + "at most one call."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("known-name-simulation-success-mass"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.success_mass_le_simulated_add_guessed_hit"),
                H("Only a successful unknown-name query can change the result"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Sample an oracle world from an arbitrary probability mass function and "
                    + "run the original deterministic strategy and the simulation on that same "
                    + "world with the same initial known set. A successful reply adds its queried "
                    + "name and neighbor names to the current set. For any success predicate of "
                    + "the world and completed record, the "
                    + "original success probability is at most the simulated success probability "
                    + "plus the probability that the original strategy hits a name outside its "
                    + "current known set. The two records agree up to that hit. A real miss on "
                    + "an unknown name and a synthetic miss select the same continuation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("known-name-next-query-from-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/KnownNameSimulation.nextQuery_of_prefix"),
                H("The actual transcript prefix determines the next query"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Run the same strategy with and without truncation after a fixed number "
                    + "of steps against the same oracle. Applying the next-query readout to the "
                    + "truncated record returns the queried label at that index in the full "
                    + "record. If the full run has already stopped, the readout returns none."))),
                DescribeRole.Theorem))));
}
