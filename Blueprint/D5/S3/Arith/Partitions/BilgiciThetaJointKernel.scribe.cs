using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaJointKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaJointKernel.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The joint kernel of the two detectors.",
        H("The joint kernel of the two detectors"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-joint-kernel"),
                DeclarationHandle.Create(Prefix + "joint_kernel"), H("The cubic multiplication range"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("On the character-four subspace of degree seven and weight eleven, the joint kernel is "
                    + "exactly the image of multiplication by the invariant cubic from degree four and weight "
                    + "nine of the same character. Two projected words give independent detector columns, and "
                    + "two cubic multiples are independent by their trace coefficients. The four-word upper "
                    + "bound then makes these four classes a basis."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-detector-coordinates"),
                DeclarationHandle.Create(Prefix + "kernel_coordinates"), H("Coordinates after the detector tests"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The two tests take the values (17, 13) and (0, 1) on the projected words "
                    + "5899999 and 1234699. Their vanishing forces both projected-word coefficients to vanish, "
                    + "leaving only the two cubic multiples."))), DescribeRole.Theorem))));
}
