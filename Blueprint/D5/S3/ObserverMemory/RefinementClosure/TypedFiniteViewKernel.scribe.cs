using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementClosure;

internal sealed class TypedFiniteViewKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/RefinementClosure/TypedFiniteViewKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Typed partial labelled path views refine to full behavior at any plateau.",
        H("Typed finite path views and stable refinement"),
        Blocks(
            Paragraph(Text(
                "The types, their state and readout spaces, the named edges between types, "
                    + "and each edge's label space are arbitrary. Each edge responds partially "
                    + "with a label and a state of its target type. An absent response is "
                    + "illegality, not an extra state. No finiteness, decidable equality, "
                    + "or totality assumption is imposed.")),
            Paragraph(Text(
                "A path is a composable word of named edges in execution order. Its response "
                    + "is absent if any edge is illegal; otherwise it contains the complete "
                    + "ordered tuple of edge labels and the terminal typed readout. The "
                    + "finite view records responses to every path up to its depth, including "
                    + "every prefix and the empty path. The complete behavior records all "
                    + "finite paths. Both retain the starting type as a separate tag.")),
            Paragraph(Text(
                "The refinement relation is defined independently: depth zero requires "
                    + "equal type tags and roots; the next depth additionally requires "
                    + "simultaneous legality for every named outgoing edge and, when legal, "
                    + "equal labels and successors related at the preceding depth.")),
            Describe.Lean(
                DescribeId.Create("typed-finite-view-kernel"),
                DeclarationHandle.Create(Prefix + "typed_finite_view_kernel"),
                H("Finite views, intersection, and permanent stability"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the full disjoint union of states, refinement at any depth is "
                            + "exactly equality of the corresponding finite views. Each next "
                            + "relation is contained in the previous one, and equality of "
                            + "complete behavior is their intersection.")),
                    Paragraph(Text(
                        "If two consecutive refinement relations coincide at one depth, "
                            + "that relation already equals the complete behavior kernel. "
                            + "Every later relation equals it as well. This is a conditional "
                            + "stability certificate and does not assert that a plateau exists.")),
                    Paragraph(Text(
                        "Induction on depth splits nonempty paths at their first edge. "
                            + "One-edge responses recover legality and the first label; "
                            + "removing that label from longer responses recovers every "
                            + "successor path response. Restricting lengths gives descent, "
                            + "and each finite path belongs to its own length bound. Equality "
                            + "of consecutive relations propagates through the recurrence, "
                            + "so the path characterization identifies the plateau with "
                            + "complete behavior."))),
                DescribeRole.Theorem))));
}
