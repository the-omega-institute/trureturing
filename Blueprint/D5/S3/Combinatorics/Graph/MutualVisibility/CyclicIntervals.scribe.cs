using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.MutualVisibility;

internal sealed class CyclicIntervalsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/GraphInvariants/fresanfigueroa2026mutualvisibility");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Auxiliary finite cut-counting structure for mutual-visibility reconfiguration.",
        H("CyclicIntervals"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("high-rank-component"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/MutualVisibility/CyclicIntervals.high_rank_component"),
                H("A component above rank two has a small-degree member"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Fix one surviving component after an actual configuration cut. If all its configurations have at least three labels, some configuration in it has degree at most the cut size."))),
                DescribeRole.Theorem),
            Paragraph(Text("Proper nonempty cyclic intervals have a unique initial vertex: it is selected and its predecessor is not. Their distinct starts supply disjoint deletion chains. The finite-index construction transports these intervals through an injective labeling of an arbitrary selected set. If a surviving component has no configuration of rank below three, choose a configuration of maximum rank m. Its m internal cyclic deletion chains end at forbidden singletons and yield m distinct cuts. For each outside label, every actual slide starts a separate chain of proper y-containing cyclic intervals ending at a forbidden pair. The proper-chain count requires only exclusion of its two-label endpoints and remains valid when larger or unrelated two-label configurations survive. The unique interval start separates these chains. Any feasible addition has rank m+1 and is itself cut, separately from those proper chains. Partitioning actual neighbors by their unique outside label and combining the disjoint cut classes gives a vertex of degree at most the cut size.")))));
}
