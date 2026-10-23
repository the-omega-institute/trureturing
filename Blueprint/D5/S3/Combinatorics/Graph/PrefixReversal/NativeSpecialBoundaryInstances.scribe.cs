using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeSpecialBoundaryInstancesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeSpecialBoundaryInstances.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Even and Odd Native Boundary Assemblies.",
        H("Even and Odd Native Boundary Assemblies"),
        Blocks(
            Describe.Lean(DescribeId.Create("native-special-child-even-path"), DeclarationHandle.Create(Prefix + "native_special_child_even_path"),
                H("Consume a Complete Actual Even Boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k=2s+2, a Hamilton cycle on the native special child with a complete actual special-cut partition and the precise even boundary endpoint relation yields a Hamilton path from right port zero to left port k. The literal route, support counts and retained-edge inventory are constructed from those supplied paths."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-special-child-odd-path"), DeclarationHandle.Create(Prefix + "native_special_child_odd_path"),
                H("Consume a Complete Actual Odd Boundary"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For k=2s+3, a Hamilton cycle on the native special child with a complete actual special-cut partition and the precise odd boundary endpoint relation yields a Hamilton path from right port zero to left port k. Every output edge belongs to the joined actual paths or a proved native seam; the previous cycle and boundary partition remain inputs."))), DescribeRole.Theorem))));
}
