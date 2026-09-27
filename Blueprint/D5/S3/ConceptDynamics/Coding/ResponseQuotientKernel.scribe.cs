using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class ResponseQuotientKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual numbered finite path lifts define a response kernel; depth zero remembers the state and increasing depth can only forget information.",
        H("Response quotient kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("response-kernel-zero-and-step"),
                DeclarationHandle.Create("D5/S3/ConceptDynamics/Coding/ResponseQuotientKernel.response_zero_and_step"),
                H("Finite path responses are nested"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A numbered finite path is lifted from its terminal state by the actual incoming edge map. The resulting response readout records the projected state and every lifted path endpoint. At depth zero, the empty path recovers the original state exactly. Extending a path by one edge only adds coordinates computed from the previous readout, so equality at depth d implies equality at depth d+1."))),
                DescribeRole.Theorem))));
}
