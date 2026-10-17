using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.PrefixReversal;

internal sealed class NativeActualJ2JointPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/PrefixReversal/NativeActualJ2JointPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six actual native components partition the support and uncut edges of the same supplied cycle.",
        H("Same-Cycle Native Joint Components"),
        Blocks(
            Paragraph(Text("The native J2 six-component theorem specifies the endpoint table independently of a selected cycle. The conclusions below lift those paths to a domain whose actual vertices are precisely the full F2 domain. The same supplied Hamiltonian cycle and its exact native inventory are used throughout; these results do not assert an all-order recursive construction.")),
            Describe.Lean(DescribeId.Create("native-actual-j2-joint-paths"),
                DeclarationHandle.Create(Prefix + "native_actual_j2_joint_paths"),
                H("Six Components of the Supplied Cycle"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For m at least five, the six actual simple paths keep their literal componentStartPort and componentFinishPort endpoints. Their supports cover every domain vertex once and are a permutation of the supplied cycle support tail. Their concatenated edges are a permutation of exactly the supplied cycle edges outside the six independent marked cuts. Every marked cut belongs to that same cycle. No support partition or target retained-edge certificate is assumed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-actual-j2-frame-joint-paths"),
                DeclarationHandle.Create(Prefix + "native_actual_j2_frame_joint_paths"),
                H("Preserve the Same Components in an Arbitrary Frame"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Left label relabelling maps the six actual components into the complete independent domain of any two-label supply frame. The indexed endpoint table, simple-path property, full support permutation and exact edge permutation are retained against the same mapped cycle. The six cuts are mapped pointwise by the same graph isomorphism."))), DescribeRole.Theorem))));
}
