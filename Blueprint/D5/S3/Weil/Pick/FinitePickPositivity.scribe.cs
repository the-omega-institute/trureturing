using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class FinitePickPositivityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/FinitePickPositivity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive Hermitian kernels and contractive scalar multipliers are characterized by finite Pick matrix positivity.",
        H("Finite Pick Positivity"),
        Blocks(
            Def("positive", "IsPositiveKernel", "Positive Hermitian kernel",
                "Every finite sampled Gram matrix of the Hermitian kernel is positive semidefinite."),
            Def("matrix", "finitePickMatrix", "Finite scalar Pick matrix",
                "The kernel Gram entry is multiplied by one minus the proposed multiplier outer product."),
            Def("contractive", "IsKernelContractiveMultiplier", "Kernel-contractive multiplier",
                "Every finite Pick matrix of the scalar function is positive semidefinite."),
            Thm("hermitian", "finitePickMatrix_isHermitian", "Pick matrices are Hermitian",
                "Conjugate symmetry of the kernel and multiplier factor makes every finite Pick matrix Hermitian."),
            Thm("zero-matrix", "finitePickMatrix_zero", "Zero multiplier recovers the Gram matrix",
                "The Pick matrix of the zero function is exactly the original sampled kernel matrix."),
            Thm("zero-contractive", "zero_isKernelContractiveMultiplier", "Zero is contractive for positive kernels",
                "Positive-kernel Gram matrices certify the zero multiplier."),
            Def("zero-kernel", "zeroHermitianKernel", "Zero Hermitian kernel",
                "The identically zero kernel provides the additive neutral positive kernel."),
            Thm("zero-positive", "zeroHermitianKernel_isPositive", "The zero kernel is positive",
                "All finite Gram matrices of the zero kernel are zero positive-semidefinite matrices."),
            Thm("all-zero", "every_multiplier_contracts_zeroKernel", "Every multiplier contracts the zero kernel",
                "Every finite Pick matrix over the zero kernel vanishes.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/HermitianKernelNegativeSquares")),
        ]));

    private static DocumentBlock.Describe Def(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Definition);

    private static DocumentBlock.Describe Thm(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))), DescribeRole.Theorem);
}
