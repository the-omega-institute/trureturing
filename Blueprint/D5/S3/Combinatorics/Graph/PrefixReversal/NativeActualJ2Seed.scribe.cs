using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualJ2SeedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2Seed.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete native two-order seed uses one actual cycle and one actual inventory throughout.",
        H("One Actual Seed for Both Native Orders"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-actual-j2-seed"), DeclarationHandle.Create(Prefix + "native_actual_j2_seed"),
                H("Earn the Complete Same-Cycle Seed"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every m at least five and every supplied two-label frame, one raw F2 Hamilton witness is selected and mapped once. Its six joint pieces and both three-piece half families retain their indexed native endpoint tables. The joint cuts are the disjoint union of the two half cut groups; all three support and filtered-edge permutations refer to that same cycle. The seed earns the protected-a edge invariant with the actual final two selected labels, the remaining-b edge invariant outside the selected set, and the selected-c invariant. The protected pair correspondence follows from the raw zero-port coordinates and the frame relabelling, without weakening the excluded pair to arbitrary selected labels. The opposite half retains its exceptional literal barred table. This is a two-label seed, distinct from the crossing-state shape required starting at the third order. The all-order construction remains a separate obligation."))), DescribeRole.Theorem))));
}
