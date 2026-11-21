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
                DescribeRole.Theorem))));
}
