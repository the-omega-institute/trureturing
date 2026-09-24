using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PartialIdentification;

internal sealed class EnabledPathSwapConnectivityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Enabled paths between lower sets of a finite poset are precisely linear extensions of their " +
        "difference and are connected by legal adjacent incomparable exchanges.",
        H("Enabled Paths and Adjacent Exchanges"),
        Blocks(
            Paragraph(Text(
                "Let E be a finite partially ordered set, and let I and J be lower sets with I " +
                "contained in J. An event is enabled at a cut K when it is absent from K and every " +
                "strict predecessor belongs to K. An execution adds its listed events in order and ends " +
                "at the specified final cut. Freshness excludes repeated events and events already in " +
                "I. Adding an enabled event to a lower set again gives a lower set, so every reached " +
                "prefix is a legal cut.")),
            Paragraph(Text(
                "An extension list has no repetitions, contains exactly the events in J outside I, and " +
                "has no later event less than or equal to an earlier event in the original partial " +
                "order. This is an independent order description of the lists. The no-repetition and " +
                "support conditions identify the induced gap with the positions from zero to the list " +
                "length minus one. If two distinct gap events satisfy the original precedence relation, " +
                "their occurrence positions increase: the opposite positional order would violate the " +
                "pairwise condition. Transporting the total order of positions therefore gives a linear " +
                "extension of the induced gap. Conversely, enumerating any total extension of that " +
                "finite induced order gives exactly these support, no-repetition, and pairwise " +
                "properties.")),
            Describe.Lean(
                DescribeId.Create("enabled-path-swap-connectivity"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Correspondence, existence, and legal swap connectivity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every event list, execution from I to J is equivalent to being an " +
                        "extension list of the gap. At least one such execution exists. For every two " +
                        "executions from I to J, the first is related to the second by the reflexive " +
                        "transitive closure of legal adjacent swaps. Each swap includes both complete " +
                        "executions, a literal common prefix and suffix, the actual cut reached by that " +
                        "prefix, lower closure of that cut, and two incomparable events both enabled " +
                        "there. There is no nonempty hypothesis on E or on the gap.")),
                    Paragraph(Text(
                        "For the forward correspondence, induction on an execution gives containment of " +
                        "the initial cut in the final cut, exact gap support, freshness, and the " +
                        "pairwise precedence condition. For the reverse direction, any strict " +
                        "predecessor of the head lies in J by lower closure. If it were absent from the " +
                        "current cut, it would occur later in the list, contradicting the pairwise " +
                        "condition. The tail is the extension list for the cut with the head inserted. " +
                        "Induction then constructs the execution.")),
                    Paragraph(Text(
                        "Existence uses a total relation extending the ambient partial order and sorts " +
                        "the finite gap with that explicit relation. Sorting supplies exact support and " +
                        "no repetitions. Antisymmetry of the extension relation rules out a later event " +
                        "preceding an earlier one in the original order. The ambient partial order " +
                        "itself is unchanged throughout this construction.")),
                    Paragraph(Text(
                        "For connectivity, choose the head a of the target execution and locate it in " +
                        "the other list as a prefix followed by a and a suffix. Move a left across that " +
                        "prefix. Each crossed event b is incomparable with a: either strict comparison " +
                        "would require one of these fresh events to have already occurred before the " +
                        "other could be enabled. At the common prefix cut K, both events are enabled. " +
                        "Each remains enabled after inserting the other, and the two insertions give " +
                        "the same cut. Thus the same suffix executes after both sides of the square, " +
                        "and each exchanged list is an actual legal execution.")),
                    Paragraph(Text(
                        "After a reaches the front, fix this common first event and apply induction to " +
                        "the target tail from the cut with a inserted. Prefixing a to each tail swap " +
                        "preserves its reached cut and common suffix, so the lifted chain joins the " +
                        "preceding exchanges. An empty target forces an empty source by exact gap " +
                        "support; this also includes equal endpoint cuts and an empty event type. The " +
                        "shared-prefix and shared-suffix squares are the form needed to transport " +
                        "endpoint-dependent maps or additive path costs."))),
                DescribeRole.Theorem))));
}
