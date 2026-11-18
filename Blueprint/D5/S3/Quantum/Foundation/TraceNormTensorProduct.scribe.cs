using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class TraceNormTensorProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Trace norm of a tensor product.",
        H("Trace norm of a tensor product"),
        Blocks(Describe.Lean(
            DescribeId.Create("tracenormtensorproduct"),
            DeclarationHandle.Create("D5/S3/Quantum/Foundation/TraceNormTensorProduct.traceNorm_kronecker"),
            H("Trace norm of a tensor product"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The trace norm of the Kronecker product of two finite rectangular complex matrices is the product of their trace norms. The positive square roots of their Gram matrices form the positive square root of the tensor Gram matrix, and the trace factors. The declaration retains its XuImaiGuhneSimultaneousUnboundedness.Toolkit namespace."))),
            DescribeRole.Theorem))));
}
