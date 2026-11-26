using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Queries;

internal sealed class NamedNeighborhoodHistoryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Partial information from complete named neighborhood queries.",
        H("Replaying a named graph transcript"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("named-neighborhood-history-fiber"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory.history_fiber_iff"),
                H("The consistent naming assignments in one transcript fiber"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix a simple graph, a deterministic adaptive protocol, and a reference "
                        + "injection from vertices to names. The oracle returns all neighbor names "
                        + "as an unordered set on a hit and a separate failure marker on a miss. "
                        + "The observed names are the initially supplied names, successful query "
                        + "names, and returned neighbor names. Every initially supplied name "
                        + "belongs to a vertex of the reference graph.")),
                    Paragraph(Text(
                        "Require the candidate injection to agree with the reference injection "
                        + "at all vertices with observed names. The candidate then replays the "
                        + "record exactly if every other vertex receives a name outside the "
                        + "observed set and outside the recorded misses. Agreement at the queried "
                        + "vertices and all returned neighbors reproduces the successful replies. "
                        + "Avoiding the misses reproduces the failures."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("named-neighborhood-fresh-name-hit"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/Queries/NamedNeighborhoodHistory.conditional_unseen_name_hit"),
                H("The exact fresh-name hit probability after the actual transcript"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For finite vertex and name types, condition a uniform injection on the "
                        + "actual transcript and agreement on the initially supplied names. The "
                        + "condition leaves a nonempty set because the reference injection itself "
                        + "belongs to it. Under the conditional law, the probability that any "
                        + "specified fresh name labels some vertex is the number of vertices minus "
                        + "the number of observed names, divided by the number of names outside "
                        + "both the observed set and the recorded misses.")),
                    Paragraph(Text(
                        "The vertices carrying the later observed names can vary across the "
                        + "compatible namings. Swapping any two fresh names leaves every recorded "
                        + "reply and initial assignment intact and pairs the corresponding hit "
                        + "events. Each compatible naming occupies the same number of fresh names, "
                        + "so counting incidences by name and by compatible naming yields the mass."))),
                DescribeRole.Theorem))));
}
