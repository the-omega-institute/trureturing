using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;

internal sealed class ModularTransferTensorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Hilbert–Schmidt transfer operator represents a reflected correlation in the Hilbert tensor product.",
        H("Hilbert tensor representation of a modular transfer"),
        Blocks(Describe.Lean(
            DescribeId.Create("modular-transfer-tensor"),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/ModularTransferTensor.transfer_tensor"),
            H("Correlation vector and its squared norm"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For a Hilbert–Schmidt operator T on a complete complex Hilbert space and "
                + "a norm-preserving reflection satisfying the symmetric pairing identity, "
                + "the reflected matrix coefficients are the inner products of a single "
                + "vector with elementary tensors. The squared norm of the vector is the "
                + "real trace of the positive operator T†T. The proof expands in a Hilbert "
                + "basis and takes an unconditional limit in the completed tensor product. "
                + "This is the Hilbert space step in the order-two sewing argument for Jia, "
                + "arXiv:2611.34922v1, equation (14). The modular transfer and the weighted "
                + "noncommutative L² identification enter the CFT application as additional data."))),
            DescribeRole.Theorem))));
}
