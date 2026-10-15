using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeOuterChildAssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeOuterChildAssembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Construct the Complete Native Parent from Independent Children.",
        H("Construct the Complete Native Parent from Independent Children"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-parent-cycle-of-child-paths"), DeclarationHandle.Create(Prefix + "native_parent_cycle_of_child_paths"),
                H("Earn Full Parent Hamiltonicity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual Hamilton paths on every independently defined native child, with their literal native endpoints, are joined in supply order into one Hamilton cycle on the full parent domain. Disjoint child domains prove disjoint support, the independent insertion partition proves complete parent coverage, and native c-generator seams close the same actual cycle. Its raw start, support and edge inventories are retained."))), DescribeRole.Theorem))));
}
