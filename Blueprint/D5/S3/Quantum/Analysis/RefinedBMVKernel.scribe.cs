using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient kernel with a positive center",
        H("The coefficient kernel with a positive center"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refinedbmvkernel-kernel-pos-psd"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVKernel.kernel_pos_psd"),
                H("The coefficient kernel with a positive center"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With a zero among the remaining entries, the Schur complement reduces the coefficient matrix to a two-dimensional inequality. The zero-center case comes from a Cauchy kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("refinedbmvkernel-symmetric-kernel-psd"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVKernel.symmetricKernel_psd"),
                H("Positivity of the symmetric coefficient kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each centered coefficient matrix is positive semidefinite for an arbitrary finite list of nonnegative eigenvalues. A positive center uses the sum of a rank-one matrix and a Cauchy congruence. At a zero center the rank-one term vanishes."))),
                DescribeRole.Theorem))));
}
