using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeMarkedCutRetentionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedCutRetention.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Preserve Protected a and Remaining b Edges Through Native Recursion.",
        H("Preserve Protected a and Remaining b Edges Through Native Recursion"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-b-edges-distinct-terminals"), DeclarationHandle.Create(Prefix + "native_b_edges_distinct_terminals"),
                H("Terminal Labels Distinguish Undirected b Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both ends of an actual b edge keep the same terminal label. Actual undirected b edges with distinct terminal labels therefore differ, regardless of orientation."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-remaining-b-not-special-cut"), DeclarationHandle.Create(Prefix + "native_remaining_b_not_special_cut"),
                H("Remaining-Terminal b Edges Are Uncut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An actual b edge in the special native domain whose terminal differs from the supplier terminal cannot be any supplier cut."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-special-path-keeps-remaining-b"), DeclarationHandle.Create(Prefix + "native_special_path_keeps_remaining_b"),
                H("Special Joining Retains an Actual Remaining b Edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact uncut-piece inventory of a supplied cycle and the literal joined chain preserve every actual previous b edge with a terminal different from the supplier terminal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-other-path-keeps-remaining-b"), DeclarationHandle.Create(Prefix + "native_other_path_keeps_remaining_b"),
                H("Ordinary Opening Retains Remaining b Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The supplied ordinary complement path removes exactly its supplier b edge. An actual previous b edge with a different terminal therefore belongs to that same path."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-parent-cycle-keeps-child-path-edges"), DeclarationHandle.Create(Prefix + "native_parent_cycle_keeps_child_path_edges"),
                H("The Parent Retains Every Actual Child-Path Edge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the literal closed parent edge chain associated with the supplied lifted child paths, every actual edge of each child path occurs in the raw edge list of that same parent cycle. No new child path or cycle is selected."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-parent-cycle-keeps-remaining-b"), DeclarationHandle.Create(Prefix + "native_parent_cycle_keeps_remaining_b"),
                H("Earn the Parent Remaining b Invariant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The unique native child-layer partition and the actual parent chain transfer the supplied child-path b retention law to the same parent cycle. The terminal guard excludes both the old selected labels and the supplier terminal."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-a-changes-terminal"), DeclarationHandle.Create(Prefix + "native_a_changes_terminal"),
                H("Full Reversal Changes the Terminal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On an actual native configuration at the stated dimension, the full reversal a changes the terminal label because the first and last positions are distinct and the configuration is injective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-a-edge-ne-b-edge"), DeclarationHandle.Create(Prefix + "native_a_edge_ne_b_edge"),
                H("Actual a Edges Differ from Supplier b Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two ends of an a edge have different terminal labels while both ends of a b edge have the same label. The resulting inequality concerns undirected edges."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-a-not-special-cut"), DeclarationHandle.Create(Prefix + "native_a_not_special_cut"),
                H("No Actual a Edge Is a Supplier Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual a edge in the native special child differs from each supplier b cut, independently of the protected terminal pair."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-special-path-keeps-a"), DeclarationHandle.Create(Prefix + "native_special_path_keeps_a"),
                H("Special Joining Retains Previous a Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Only supplier b edges are removed from the supplied special cycle. The exact uncut-piece inventory and joined chain therefore preserve every previous actual a edge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-other-path-keeps-a"), DeclarationHandle.Create(Prefix + "native_other_path_keeps_a"),
                H("Ordinary Opening Retains Previous a Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An ordinary complement path removes its single supplier b edge. Its exact inventory preserves every actual a edge of the supplied child cycle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-cut-retention-native-parent-cycle-keeps-protected-a"), DeclarationHandle.Create(Prefix + "native_parent_cycle_keeps_protected_a"),
                H("Earn the Parent Protected a Invariant"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The native child-layer partition and actual parent edge chain transfer each supplied child-path a retention law to this same parent cycle. The guard excludes exactly the fixed protected terminal pair; previously missing a edges are not claimed to have been restored."))), DescribeRole.Theorem))));
}
