using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ArbitraryRootEventMomentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Geometric event caps control square increments even when events switch between arbitrary roots.",
        H("Geometric Event Moments on Arbitrary Roots"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("arbitrary-root-event-load"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ArbitraryRootEventMoment.eventLoad"),
                H("The event load"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each entry in a finite list contains a root label and a finite event. "
                    + "At a point x, eventLoad sums the event indicators. Repeated entries "
                    + "are counted separately, and the empty list has load zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("geometric-root-event-caps"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ArbitraryRootEventMoment.geometricRootCaps"),
                H("Geometrically decreasing root caps"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a nonnegative weight mu on a finite carrier X and a root map "
                    + "from X to an arbitrary type I. Each event must lie in its labelled "
                    + "root and have mu-mass at most the current cap for that root. All "
                    + "caps are multiplied by r after every event. The predicate accepts "
                    + "the empty list without further conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("arbitrary-root-event-moment"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Congruence/ArbitraryRootEventMoment.arbitrary_root_event_moment_le"),
                H("A common constant-root budget controls arbitrary switching"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let 0 <= r < 1, let d(i) be nonnegative initial caps, and let "
                        + "a(i) be natural initial counts. The initial real load W is "
                        + "at most 1+a(i) at every point of root i. Suppose M is "
                        + "nonnegative and bounds d(i) times ((2a(i)+3)/(1-r) "
                        + "+ 2r/(1-r)^2) for every i. Then every finite event list "
                        + "satisfying geometricRootCaps has mu-weighted square increment "
                        + "sum mu(x)((W(x)+eventLoad(x))^2-W(x)^2) at most M.")),
                    Paragraph(Text(
                        "On admitting an event in root i, the immediate square increment "
                        + "is at most c=(2a(i)+3)d(i). Increase only count i by one and "
                        + "scale all caps by r. The updated constant-root budget for i "
                        + "equals its old budget minus c. Every other updated budget is "
                        + "at most rM, while c <= (1-r)M. Thus M-c bounds every updated "
                        + "root budget, and induction applies to the actual remaining "
                        + "events and updated load. The square increments telescope.")),
                    Paragraph(Text(
                        "The weight mu need not be normalized, the roots need not be "
                        + "finite, and no event nesting is assumed. The cases r=0, an "
                        + "empty event list, and an empty root type are included. For "
                        + "a finite nonempty root type, M may be chosen as the maximum "
                        + "of the displayed constant-root costs.")),
                    Paragraph(Text(
                        "For prime-power cylinders, choose r=1/p and group points by "
                        + "their residue modulo p. If the remaining cylinders start at "
                        + "depth m, a density bound C(i) on root i gives the initial "
                        + "cap d(i)=C(i)/p^m. The constant-root cost becomes "
                        + "C(i)/p^m times (p(2a(i)+3)/(p-1)+2p/(p-1)^2). "
                        + "This keeps the separate root densities when p is at least "
                        + "five and more than two roots survive. Cylinder cap proofs "
                        + "and the other prime coordinates are separate hypotheses."))),
                DescribeRole.Theorem))));
}
