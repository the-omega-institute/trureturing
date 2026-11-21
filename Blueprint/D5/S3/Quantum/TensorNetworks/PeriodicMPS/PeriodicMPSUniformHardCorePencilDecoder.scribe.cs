using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformHardCorePencilDecoderDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformHardCorePencilDecoder";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local decoding of the ordinary trace invariants",
        H("Local decoding of the ordinary trace invariants"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorepencildecoder-exists-open-ordinarydecoder"),
                DeclarationHandle.Create(Module + ".exists_open_ordinaryDecoder"),
                H("A continuous decoder on a full-tensor neighborhood"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every n ≥ 7 there is an open neighborhood of the witness amplitude on which the ordinary decoder is continuous. The two simple roots of the recovered determinant pencil give a frame of singular core combinations. Ratios of selected amplitudes in that frame recover the four invariants normalized by the first trace and certify that this trace is nonzero. The decoding assertion holds for every scaled trace-word representation of a tensor in the neighborhood."))),
                DescribeRole.Theorem))));
}
