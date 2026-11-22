using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSUniformAntisymmetricTransferDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSUniformAntisymmetricTransfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The singlet contraction of uniform periodic trace tensors",
        H("The singlet contraction of uniform periodic trace tensors"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformantisymmetrictransfer-normalizedmarginal-singlet-factor"),
                DeclarationHandle.Create(Module + ".normalizedMarginal_singlet_factor"),
                H("The singlet contraction of uniform periodic trace tensors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized singlet readout factors through the ket and bra commutator determinants and a scalar sequence of the transfer characteristic polynomial."))),
                DescribeRole.Theorem))));
}
