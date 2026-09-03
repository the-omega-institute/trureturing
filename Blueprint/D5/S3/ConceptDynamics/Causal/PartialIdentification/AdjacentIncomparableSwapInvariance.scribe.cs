using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Causal.PartialIdentification;

internal sealed class AdjacentIncomparableSwapInvarianceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Causal/PartialIdentification/"
            + "AdjacentIncomparableSwapInvariance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Adjacent parent-independent structural updates commute, so changing a "
            + "compatible total order by one local swap preserves evaluation and readout.",
        H("Adjacent Incomparable Swap Invariance"),
        Blocks(
            Paragraph(Text(
                "A parent-local equation reads only its certified parent coordinates. "
                    + "Replacing a nonparent coordinate therefore leaves its local value unchanged.")),
            Paragraph(Text(
                "Two distinct nodes with no direct parent edge in either direction write "
                    + "different coordinates and neither equation reads the coordinate written by the other. "
                    + "Their structural updates commute.")),
            Paragraph(Text(
                "The commuting pair may occur after an arbitrary evaluated prefix and before "
                    + "an arbitrary suffix. Swapping the neighboring nodes preserves the complete final state and every readout of that state.")),
            Describe.Lean(
                DescribeId.Create("local-updates-commute-without-direct-edges"),
                DeclarationHandle.Create(
                    Prefix + "localEvaluateNode_comm_of_no_direct_edges"),
                H("Parent-independent local structural updates commute"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof reduces each local equation to the same pre-update value and then checks that writes to two distinct coordinates commute."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("parent-local-adjacent-swap-invariance"),
                DeclarationHandle.Create(
                    Prefix
                        + "parent_local_evaluation_invariant_under_adjacent_swap"),
                H("One adjacent incomparable swap preserves structural evaluation"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Induction transports the commuting pair through an arbitrary evaluated prefix. "
                        + "The common suffix is then run from equal intermediate states."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("readout-adjacent-swap-invariance"),
                DeclarationHandle.Create(
                    Prefix + "readout_invariant_under_adjacent_swap"),
                H("Every final-state readout is invariant under the swap"),
                StatementSource.FromLean(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Applying an arbitrary readout to the equal final states supplies the local query-invariance certificate needed by causal-order LP compilation."))),
                DescribeRole.Theorem))));
}
