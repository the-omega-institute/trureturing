using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Marginals;

internal sealed class BinaryDeletionDimensionDocument : IScribeDocumentDefinition
{
    private const string Dimension =
        "D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension.supportedKernel_finrank";
    private const string Recurrence =
        "D5/S3/Quantum/Entanglement/Marginals/BinaryDeletionDimension.noTriple_finrank";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Dimension of a binary deletion kernel with restricted words.",
        H("Independent coordinates of the binary deletion kernel"),
        Blocks(
            Describe.Lean(DescribeId.Create("binary-deletion-kernel-dimension"),
                DeclarationHandle.Create(Dimension), H("Exact complex dimension"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For any allowed set of binary words on finitely many sites, "
                    + "the kernel consists of matrices supported in both indices "
                    + "on those words and annihilated by every one-site deletion. "
                    + "Its complex dimension is the number of ordered patterns "
                    + "for which all assignments of the common bits are allowed.")),
                    Paragraph(Text(
                    "Read one coefficient from each pattern at the pair whose common "
                    + "bits are zero. Propagation along common-bit changes makes this "
                    + "linear map injective. For each allowed pattern, restrict a "
                    + "witness of the support criterion to that pattern and scale its "
                    + "chosen coefficient to one. The restriction preserves deletion "
                    + "cancellation since both summands have the same pattern. Summing "
                    + "these single-coordinate matrices realizes any coefficient vector."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("no-triple-deletion-kernel-dimension"),
                DeclarationHandle.Create(Recurrence), H("Dimensions on the no-111 chain"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A word is allowed on an open chain when each window of three "
                    + "sites contains a zero. In the ternary pattern that distinguishes "
                    + "agreement and the two ordered differences, each triple must "
                    + "contain both differences. This follows by setting every common "
                    + "bit to one to test the most occupied pair with that pattern.")),
                    Paragraph(Text(
                    "Counting accepted extensions of a prefix requires only the last "
                    + "two symbols. With the two orientations interchanged the counts "
                    + "agree. The resulting recurrence gives complex dimensions "
                    + "12, 24 and 44 at lengths three, four and five. Each dimension "
                    + "at length six or greater is the sum at the preceding three lengths."))),
                DescribeRole.Theorem))));
}
