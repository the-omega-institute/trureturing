using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Pick;

internal sealed class CompletePickInterpolationPropertyDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Pick/CompletePickInterpolationProperty.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Matrix-valued finite Pick data define complete kernel contractivity and a precise complete interpolation property.",
        H("Finite Complete Pick Interpolation Property"),
        Blocks(
            Def("matrix", "operatorPickMatrix", "Matrix-valued block Pick matrix",
                "Each node pair contributes the kernel scalar times the block defect from the two target matrices."),
            Def("consistent", "ConsistentMatrixInterpolationData", "Consistent repeated-node data",
                "Repeated interpolation nodes are required to carry identical matrix values."),
            Def("interpolates", "InterpolatesMatrixData", "Matrix interpolation predicate",
                "A multiplier interpolates the data when it takes every prescribed value at its node."),
            Def("contractive", "IsCompletelyKernelContractive", "Complete kernel contractivity at fixed size",
                "Every finite block Pick matrix sampled from the matrix-valued function is positive semidefinite."),
            Def("property", "HasCompletePickInterpolationProperty", "Finite complete Pick property",
                "Every consistent positive finite block Pick datum admits a completely kernel-contractive interpolant."),
            Thm("zero-matrix", "operatorPickMatrix_zeroKernel", "Zero-kernel block Pick matrices vanish",
                "Every matrix-valued Pick matrix over the zero kernel is the zero matrix."),
            Thm("zero-contractivity", "every_matrix_multiplier_contracts_zeroKernel", "Every matrix multiplier contracts the zero kernel",
                "Vanishing block Pick matrices make every matrix-valued function completely contractive over the zero kernel."),
            Def("extension", "extendConsistentMatrixData", "Classical consistent-data extension",
                "A finite consistent partial matrix assignment is extended by choosing a matching node when one exists."),
            Thm("interpolation", "extendConsistentMatrixData_interpolates", "The extension interpolates consistent data",
                "Repeated-node consistency makes the chosen finite extension independent of the selected witness."),
            Thm("inhabited", "zeroKernel_hasCompletePickInterpolationProperty", "The zero kernel has the complete property",
                "The zero kernel provides a fully checked inhabited model of the finite matrix interpolation definition.")),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/Weil/Pick/DeBrangesRovnyakKernel")),
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
