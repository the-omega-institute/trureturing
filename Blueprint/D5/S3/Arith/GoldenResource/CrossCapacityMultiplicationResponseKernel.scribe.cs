using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class CrossCapacityMultiplicationResponseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cross-Capacity Multiplication Response Kernels.",
        H("Cross-Capacity Multiplication Response Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cross-capacity-multiplication-response-kernel-classification"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/CrossCapacityMultiplicationResponseKernel.eq_plus_all_iff"),
                H("Equality of all multiplication responses"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take two natural capacity vectors on a common finite coordinate set and a bounded "
                    + "state in each box. Each letter increases its coordinate by one and fails at capacity. "
                    + "A successful word returns the parity sign of the endpoint coordinate sum when every "
                    + "coordinate is at most one, and zero otherwise; failure is a distinct value. "
                    + "The states agree on every finite word, including the empty word, exactly when their "
                    + "remaining capacities agree and one of two conditions holds. Either both initial states "
                    + "are not squarefree, or both are squarefree, their coordinate sums have equal parity, "
                    + "and their coordinates agree on every axis of positive remaining capacity. Repeated "
                    + "letters recover the entire remaining capacity on each axis. In the squarefree branch, "
                    + "on successful words, "
                    + "coordinates with zero remaining capacity stay fixed and contribute only their initial "
                    + "parity, while all other coordinates increase together. Zero capacities and an empty "
                    + "coordinate set are allowed."))),
                DescribeRole.Theorem))));
}
