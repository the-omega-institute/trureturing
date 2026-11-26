using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Semigroups;

internal sealed class WuEndpointPauliFrameDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Semigroups/WuEndpointPauliFrame.";

    private static DocumentBlock Theorem(string id, string name, string title, string statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(statement))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Anticommuting Hermitian involutions give real orthonormal frames and two bounds on sums of complex squared overlaps.",
        H("Pauli frame overlap bounds"),
        Blocks(
            Paragraph(Text("Rotating the identity slot by i gives real orthogonality. Applying the real Bessel inequality to u and iu bounds the complex squared overlaps. The ordered product of all four signed Pauli words transfers this bound to the complementary products.")),
            Theorem("real-frame", "real_orthonormal", "Real orthonormality",
                "For a unit vector, the images under symmetric anticommuting involutions and the vector rotated by i form a real orthonormal family."),
            Theorem("head-overlap", "pauli_frame_overlap_le_two", "Identity and single Pauli words",
                "The sum of the squared overlaps of u with v and with the four single-word images of v is at most 2‖u‖²‖v‖²."),
            Theorem("tail-overlap", "pauli_tail_overlap_le_two", "Triple and full Pauli products",
                "The sum of the squared overlaps of u with the four triple-word images and the full-product image of v is at most 2‖u‖²‖v‖²."))));
}
