using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyCoordinateKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic kernels and the exponent measure", H("Cyclic kernels and the exponent measure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-coordinatekernel-reduction"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction"),
                H("Reduction modulo two"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A positive cyclic two-primary coordinate maps onto ZMod 2 by the canonical reduction homomorphism. Exponent zero is excluded only from the two coordinates selected for reduction."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-coordinatekernel-reduction-kernel-eq-doubled"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateKernel.reduction_kernel_eq_doubled"),
                H("The reduction kernel is the doubled range"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reduction kills exactly twice the elements of the original cyclic coordinate. For exponent one both sides are the trivial subgroup."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("headley-coordinatekernel-reductionkernelequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateKernel.reductionKernelEquiv"),
                H("The actual decremented kernel type"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic subgroup classification identifies the literal kernel with ZMod of two to the preceding exponent. The identification uses its cardinality and includes the trivial kernel."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("headley-coordinatekernel-lower-sum-add-two"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyCoordinateKernel.lower_sum_add_two"),
                H("Strict decrease by two"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Lowering two distinct positive entries removes exactly two from their sum. Entries outside this pair remain fixed, including zero entries."))), DescribeRole.Theorem))));
}
