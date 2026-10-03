using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.GreedyBrick;

internal sealed class EventRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/GreedyBrick/EventRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuine first-zero rest trace realizes exact-reset event laws and total same-bin successors.",
        H("Events Realized by Rest Histories"),
        Blocks(
            Paragraph(Text("A rest history supplies actual RestState values and a RestEventStep "
                + "at every transition. A rest trace additionally starts at endpoint one with "
                + "capacity list [1] and initial label one, and has unbounded capacity-list length. "
                + "These are intermediate source premises; this result does not construct "
                + "the literal brick trajectory or prove the original OEIS identity.")),
            Node("greedy-brick-no-reset-budget", "Finite capacity budget", "no_reset_budget",
                "For any positive bin present at endpoint e with capacity c, suppose its label "
                + "does not occur in the next d transitions. There is an actual final capacity r, "
                + "with r plus the number of higher events equal to c. Final height is at most "
                + "initial height plus that same higher-event count. No initialization or "
                + "unbounded-height premise is needed. Absent coordinates receive no default value."),
            Node("greedy-brick-future-same-bin", "Every label returns", "future_same_bin",
                "For every event e of a rest trace, some event f strictly after e has the same bin. "
                + "If no such reset existed, unbounded higher births would exceed the finite "
                + "capacity budget of that bin. Chronological EventLaws alone are insufficient "
                + "for this existence statement."),
            Node("greedy-brick-event-laws-realization", "Exact event-law realization", "event_laws_realization",
                "The EventSequence with the trace's endpoints, labels and heights, least indices "
                + "attaining each positive height, and greatest earlier same-bin indices satisfies "
                + "every EventLaws field. Reset balance follows by telescoping the real capacity "
                + "from its prior endpoint reset to zero before the next reset, then splitting "
                + "higher events into births and renewals. Birth at height zero is unused; "
                + "positive births exist by unbounded height. Predecessors are used only at renewals."),
            Node("greedy-brick-successor-inverses", "Total immediate successors and inverse laws", "successor_inverse_laws",
                "The least future same-bin index exists for every event, is a renewal, has that "
                + "event as its immediate predecessor, and contains no intervening same-bin event. "
                + "Conversely every renewal is the successor of its predecessor. This includes "
                + "event zero and all positive-height births.")),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/Combinatorics/GreedyBrick/SuccessorBand"))]));

    private static DocumentBlock Node(string id, string title, string declaration, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
