using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeMarkedFrameDomainsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeMarkedFrameDomains.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal Native Domains for the Same Recursive Cycle.",
        H("Literal Native Domains for the Same Recursive Cycle"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-child-frame-domain"), DeclarationHandle.Create(Prefix + "native_child_frame_domain"),
                H("Rotate the Base to the Actual Child Gap"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rotating only the base list of a supplied frame to gap j gives a prior marked special domain equal to the independently defined outer child at j, for every configuration. The selected list and terminal retain their literal values."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("child-marked-domain-map-bijective"), DeclarationHandle.Create(Prefix + "child_marked_domain_map_bijective"),
                H("Identify All Child Vertices"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity map on actual configurations between the rotated prior marked domain and its independent child domain is bijective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-child-frame-specified-ordinary"), DeclarationHandle.Create(Prefix + "native_child_frame_specified_ordinary"),
                H("Earn the Actual Ordinary Supplier Cut"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Hamilton cycle on the rotated prior marked domain with its remaining-b invariant yields a specified ordinary child cycle for the parent constructor. The invariant proves that the literal supplier cut belongs to the same mapped cycle; raw support, edges and both protected selected labels are preserved."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-marked-orders-same-domain"), DeclarationHandle.Create(Prefix + "native_marked_orders_same_domain"),
                H("Selected Orders Share One Marked Domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two supplied marked frames have the same actual special domain when their selected label sets, ordered bases and terminals agree. Their ports may differ; the equality concerns every actual vertex configuration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("marked-order-domain-map-bijective"), DeclarationHandle.Create(Prefix + "marked_order_domain_map_bijective"),
                H("Reindex Marked Orders by the Identity Map"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The configuration identity between two marked orders with equal selected sets, bases and terminals is bijective, allowing both order descriptions to refer to one supplied cycle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-outer-orders-same-domain"), DeclarationHandle.Create(Prefix + "native_outer_orders_same_domain"),
                H("Selected Orders Share One Outer Parent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two outer parents obtained from frames with equal selected label sets, terminal and remaining base share every actual native parent vertex. The ordered remaining base is kept."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parent-order-domain-map-bijective"), DeclarationHandle.Create(Prefix + "parent_order_domain_map_bijective"),
                H("Identify the Two Outer Parent Orders"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The identity on actual configurations between the two equal outer parent domains is bijective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-p-marked-domain-eq-child"), DeclarationHandle.Create(Prefix + "native_p_marked_domain_eq_child"),
                H("Identify the Complete Prior P Child"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When a supplied prior base is A followed by u and A has length at least three, its entire marked special domain equals the final child of its outer frame. The proof uses the literal circular rotation, extending ownership beyond the marked endpoints."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-next-marked-domain-eq-parent"), DeclarationHandle.Create(Prefix + "native_next_marked_domain_eq_parent"),
                H("Identify the Complete Next Marked Domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual parent domain of the outer frame is exactly the next marked special domain. Prepending u to the selected list and rotating the terminal around the remaining base earns the identity for every configuration."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("parent-next-marked-map-bijective"), DeclarationHandle.Create(Prefix + "parent_next_marked_map_bijective"),
                H("Carry Every Parent Vertex to the Next Marked Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The configuration identity from the actual current parent domain to the next marked domain is bijective."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-same-parent-cycle-next-marked"), DeclarationHandle.Create(Prefix + "native_same_parent_cycle_next_marked"),
                H("Transport the Same Cycle and Its Earned Edges"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A supplied parent Hamilton cycle with protected-a and remaining-b invariants maps to the next marked domain without changing any raw configuration, support entry or edge. Both retained-edge invariants hold on this exact mapped cycle; no replacement cycle is chosen."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("p-marked-parent-lift-injective"), DeclarationHandle.Create(Prefix + "p_marked_parent_lift_injective"),
                H("Include the Complete Prior P State"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The configuration identity including the complete prior P marked domain into the actual current outer parent is injective, allowing actual prior walks and partitions to be mapped without identifying distinct vertices."))), DescribeRole.Theorem))));
}
