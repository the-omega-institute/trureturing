using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TwoRootEventMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual event-load square increments satisfy a uniform bound from two disjoint roots.",
        H("Two-Root Event Moments"),
        Blocks(Describe.Lean(
            DescribeId.Create("two-root-event-moment"),
            DeclarationHandle.Create(
                "D5/S3/Arith/Congruence/TwoRootEventMoment.two_root_event_moment_le"),
            H("From actual events to the discounted root potential"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let X be any finite type with decidable equality, mu a nonnegative "
                    + "weight on X, and root a map from X to Bool. Let d0 and d1 be "
                    + "nonnegative real numbers, a and b natural numbers, and W a real "
                    + "initial load. Assume W is at most 1+a on the false root and at "
                    + "most 1+b on the true root.")),
                Paragraph(Text(
                    "Each entry of a finite list consists of a root label and a finite "
                    + "event contained in that root. Its mu-mass is at most the current "
                    + "cap for the selected root, starting at d0 and d1. Both caps are "
                    + "divided by three after every entry. The predicate rootEventCaps "
                    + "records exactly these conditions, with the empty list admissible.")),
                Paragraph(Text(
                    "The eventLoad function sums the event indicators, counting every "
                    + "list occurrence. The mu-weighted sum of (W+eventLoad)^2 minus W^2 "
                    + "is at most 3 max(d0(a+2), d1(b+2)). Neither nesting of events nor "
                    + "normalization of mu is assumed. Empty events and either root label "
                    + "are allowed.")),
                Paragraph(Text(
                    "When a new event is present at x, disjoint roots bound the preceding "
                    + "load by the count assigned to its own root. Expanding the square "
                    + "then bounds the increment by its mass times 3 plus twice that "
                    + "count. Induction advances the actual load and the selected count "
                    + "together. The existing finite root-itinerary theorem supplies "
                    + "the final potential bound.")),
                Paragraph(Text(
                    "For a first test event in the false root, take W to be one plus "
                    + "its indicator, a=1, b=0, and starting tail caps d0/9 and d1/9. "
                    + "The remaining square increment is at most max(d0, 2d1/3); "
                    + "the initial square contributes total mass plus three times the "
                    + "first event's mass. Swapping roots gives the other branch. This "
                    + "supplies the event-to-itinerary step for ternary congruence "
                    + "layouts. The congruence-cylinder mass hypotheses and other prime "
                    + "coordinates still require their own proofs."))),
            DescribeRole.Theorem))));
}
