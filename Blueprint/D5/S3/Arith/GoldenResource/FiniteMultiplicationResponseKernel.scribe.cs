using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.GoldenResource;

internal sealed class FiniteMultiplicationResponseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Multiplication Response Kernels.",
        H("Finite Multiplication Response Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-multiplication-response-kernel-classification"),
                DeclarationHandle.Create("D5/S3/Arith/GoldenResource/FiniteMultiplicationResponseKernel.eq_plus_iff"),
                H("Classification at a positive finite horizon"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fix a finite set of coordinates, a natural capacity on each coordinate, and a horizon "
                    + "of at least one. States are natural vectors bounded by these capacities. A multiplication "
                    + "letter increases its coordinate by one and fails at capacity. Successful words return "
                    + "the parity sign of the coordinate sum when every endpoint coordinate is at most one, "
                    + "and zero otherwise. Failure is distinct from every successful readout, including zero. "
                    + "Two states have equal responses to every word of length at most the horizon exactly "
                    + "when they are equal, or both are not squarefree and their remaining capacities agree "
                    + "after coordinatewise truncation at the horizon. Thus each squarefree state is a "
                    + "singleton, while truncated remaining capacity classifies the other states. Zero "
                    + "capacities and an empty coordinate set are allowed."))),
                DescribeRole.Theorem))));
}
