using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualJ2HalfPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2HalfPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both restored three-piece native partitions use the same supplied actual cycle and keep their literal endpoint tables.",
        H("Actual Native Half Partitions"),
        Blocks(
            Paragraph(Text("The independent raw half-component theorem earns the three endpoint pairs. These results lift those paths into the complete domain of the supplied F2 cycle and recover that exact cycle's uncut edge inventory. They retain the literal barred exception of the opposite half, rather than assuming a generic E2 endpoint pattern. Their downstream consumer initializes both half partitions alongside the six joint pieces on one actual seed cycle; higher-order existence is a separate obligation.")),
            Describe.Lean(DescribeId.Create("native-actual-j2-half-paths"),
                DeclarationHandle.Create(Prefix + "native_actual_j2_half_paths"),
                H("Three Half Paths of the Supplied Actual Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least five and either cut side, the three actual simple paths have endpoints given by halfStart and halfFinish. Every domain vertex occurs in exactly one path, their supports permute the supplied Hamilton cycle's support tail, and their concatenated edges permute exactly its edges outside the chosen three half cuts. Every cut belongs to the supplied cycle. The domain is identified independently with F2Domain; neither a support partition nor a retained-edge certificate is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-j2-frame-half-paths"),
                DeclarationHandle.Create(Prefix + "native_actual_j2_frame_half_paths"),
                H("Transport the Same Half Partition Into a Native Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same raw Hamilton cycle is mapped once by the frame-domain graph isomorphism. Left relabelling preserves the indexed endpoint table, simple paths, exact support permutation and filtered edge permutation. Its three cuts are the images of the actual raw half cuts under that same isomorphism. The explicit target is the independently defined FrameDomain of the supplied two-label frame."))), DescribeRole.Theorem))));
}
