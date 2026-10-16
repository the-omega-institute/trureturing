using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeJ2ParentRetentionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeJ2ParentRetention.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same actual outer J2 parent inherits all three retained-edge invariants from its saved suppliers and literal openings.",
        H("Retained Edges of the Actual J2 Outer Parent"),
        Blocks(Describe.Lean(DescribeId.Create("native-j2-outer-parent-retention"),
            DeclarationHandle.Create(Prefix + "native_j2_outer_parent_retention"),
            H("Earn Protected a, Remaining b and Selected c on One Parent"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For dimension m at least five, a two-selected-label supply frame with base A followed by u, and A of length at least three, take any actual OuterParentWitnessFor W. Its same W.cycle keeps every a edge except the fixed protected terminal-label pair, keeps every b edge whose terminal is outside the old selected labels together with u, and has no c edge with terminal outside that enlarged selected set. The old P supplier, outer Q supplier and every other child seed remain those retained in W. Identity domain maps preserve their seed invariants; actual openings remove only supplier b edges; the literal parent edge inventory retains every child-path edge and exhausts all new c seams. No alternative parent cycle is chosen. This earns edge invariants for the exceptional third-order base, while the actual joint and restored-half partitions and the general induction remain separate proof obligations."))),
            DescribeRole.Theorem))));
}
