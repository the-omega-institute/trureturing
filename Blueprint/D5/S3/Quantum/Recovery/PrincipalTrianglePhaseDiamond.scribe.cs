using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class PrincipalTrianglePhaseDiamondDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A tagged pure input realizes a lossless matrix-unit test for the unhalved native diamond distance.",
        H("Native stabilized channel witness for the principal phase bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rt-native-lossless-entry-witness"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.matrixUnit_le_diamondDistance"),
                H("Lossless matrix-unit test"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two reference tags yield half of the tested matrix-unit coefficient in the output "
                    + "cross block. The pair of phase-swap unitaries recovers its doubled modulus in the "
                    + "Hermitian output difference, so the two scales cancel exactly. This proof uses the "
                    + "native density-state supremum, without a non-Hermitian input convention."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-near-real-diamond"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.near_real_diamond_lower_of_dominance"),
                H("Native diamond-distance phase lower bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For the specified channel coefficient correspondence and cross-entry dominance of the "
                    + "records, the native unhalved diamond distance obeys the quadratic near-real bound. The "
                    + "coefficient correspondence and the dominance are hypotheses: no arbitrary-channel "
                    + "reduction or unrestricted recovery obstruction is claimed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rt-native-paired-dilation-phase"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Recovery/PrincipalTrianglePhaseDiamond.paired_near_real_diamond_lower"),
                H("Paired-dilation application"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Gram of the actual correct-output dilation coordinates is positive. "
                    + "For an isometric dilation, the Gram of the omitted coordinates gives "
                    + "its within-fibre defect, without a no-leakage assumption. The two "
                    + "forward records produce the tested paired coefficient with the "
                    + "displayed conjugation, while channel and target identification "
                    + "remain hypotheses."))),
                DescribeRole.Theorem))));
}
