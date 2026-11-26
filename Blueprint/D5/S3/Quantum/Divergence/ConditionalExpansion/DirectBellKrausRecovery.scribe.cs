using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence.ConditionalExpansion;

internal sealed class DirectBellKrausRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Divergence/ConditionalExpansion/DirectBellKrausRecovery.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conjugate reshaping of a Bell-complement kernel family gives Kraus operators for exact recovery.",
        H("Direct Bell-kernel recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("amplify-kraus"),
                DeclarationHandle.Create(Module + "amplifyKraus"),
                H("Kraus amplification"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Amplification on the second factor is the sum of congruences "
                    + "by the reference identity tensored with the input Kraus operators. "
                    + "When the Kraus family represents a channel, the sum agrees "
                    + "entrywise with applying the channel to each reference block."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bell-recovery-kraus"),
                DeclarationHandle.Create(Module + "bellRecoveryKraus"),
                H("Recovery Kraus operators"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a vector vⱼ indexed by A × B, the recovery operator has entry "
                    + "at (a, b) equal to the conjugate of vⱼ(a, b) divided by √|A|."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("direct-bell-kernel-recovery"),
                DeclarationHandle.Create(Module + "direct_bell_kernel_recovery"),
                H("Exact scalar recovery from the kernel projection"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let P be the normalized Bell projector and B₀ the Kraus "
                        + "amplification of I − P. Suppose the outer products of vⱼ "
                        + "sum to Q, the projection onto the kernel of B₀. The "
                        + "reshaped recovery operators have effect Trₐ(Q)/d ≤ I. "
                        + "Their sum of congruences is completely positive.")),
                    Paragraph(Text(
                        "Each input Kraus operator, when composed with each recovery "
                        + "operator, is a scalar times the identity. This follows "
                        + "because pulling a kernel vector back through an amplified "
                        + "input Kraus operator puts it in the Bell line. The sum of "
                        + "squared scalar moduli is Tr(QX₀)/d², where X₀ is the amplified "
                        + "Bell projector. Thus the composite acts by this nonnegative "
                        + "real scalar on every input matrix."))),
                DescribeRole.Theorem))));
}
