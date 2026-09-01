using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class DeBrangesRovnyakKernelDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/DeBrangesRovnyakKernel.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Scalar multiplier defects form Hermitian de Branges-Rovnyak kernels whose Gram matrices are exactly finite Pick matrices.",
        H("de Branges-Rovnyak Defect Kernel"),
        Blocks(
            Def("kernel", "deBrangesRovnyakKernel", "Scalar defect kernel",
                "The original kernel is multiplied by one minus the multiplier outer product."),
            Thm("gram", "deBrangesRovnyakKernel_gramMatrix", "Defect Gram equals Pick matrix",
                "Sampling the defect kernel produces exactly the generic finite Pick matrix."),
            Thm("positive", "isPositiveKernel_deBrangesRovnyak_iff", "Positivity equals kernel contractivity",
                "The multiplier is kernel-contractive exactly when its de Branges-Rovnyak defect kernel is positive."),
            Thm("zero", "deBrangesRovnyakKernel_zero", "Zero multiplier preserves the kernel",
                "The zero scalar multiplier leaves every kernel entry unchanged."),
            Thm("one", "deBrangesRovnyakKernel_one", "Unit multiplier annihilates the defect",
                "The constant multiplier one makes the complete defect kernel vanish."),
            Thm("zero-positive", "deBrangesRovnyakKernel_zero_positive", "Positive kernels remain positive at zero multiplier",
                "The zero-multiplier defect inherits positivity from the original kernel."),
            Thm("one-positive", "deBrangesRovnyakKernel_one_positive", "Unit-multiplier defect is positive",
                "The zero defect kernel is positive semidefinite."),
            Thm("pick-one", "finitePickMatrix_one", "Unit-multiplier Pick matrix vanishes",
                "Every finite Pick matrix of the constant unit multiplier is zero.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/FinitePickPositivity")),
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
