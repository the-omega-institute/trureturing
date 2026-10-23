using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeRecursiveExpansionDomainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeRecursiveExpansionDomains.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal native deletion assigns every supplied cut to exactly one independent insertion child.",
        H("Actual Native Insertion Child Domains"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-child-gap-partition"), DeclarationHandle.Create(Prefix + "native_child_gap_partition"),
                H("All Independent Insertion Children"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The complete parent deletion layer is partitioned by the independently specified cyclic insertion gaps of the actual frame base. Each actual parent vertex belongs to one and only one child. A base of length at least three earns orientation separation; parent coverage is a conclusion."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-supply-child-coordinates"), DeclarationHandle.Create(Prefix + "native_supply_child_coordinates"),
                H("Literal Deletion Coordinates"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Deleting the selected labels from each actual right and left port gives the specific residual child circle and its reverse. The supplyGap function is calculated from the native position: the first k plus one cuts belong to gap zero, and every later position belongs to its literal positive gap."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-supply-cut-child-domain"), DeclarationHandle.Create(Prefix + "native_supply_cut_child_domain"),
                H("Both Endpoints Belong to Their Child"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both endpoints of every supplied b cut lie in the independent child calculated by the deletion-coordinate theorem. The conclusion concerns actual configurations, without defining membership from a skeleton edge."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-supply-cut-owner-iff"), DeclarationHandle.Create(Prefix + "native_supply_cut_owner_iff"),
                H("The Calculated Owner Is Unique"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Complete child-domain uniqueness makes the coordinate computation an equivalence: either endpoint lies in a particular child exactly when its computed supply gap equals that child index. It cannot occur in another child."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-special-child-cut-indices"), DeclarationHandle.Create(Prefix + "native_special_child_cut_indices"),
                H("Exactly the Special-Child Positions"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The special insertion child contains precisely supplier positions zero through k. This follows from the actual owner computation and the explicit native index map, without supplying a target cut count."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-other-child-unique-cut"), DeclarationHandle.Create(Prefix + "native_other_child_unique_cut"),
                H("One Actual Cut per Ordinary Child"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each positive insertion gap has one and only one actual supplier cut, at position k plus its gap index. Both existence and uniqueness follow from literal tuple deletion and the computed child owner."))), DescribeRole.Theorem))));
}
