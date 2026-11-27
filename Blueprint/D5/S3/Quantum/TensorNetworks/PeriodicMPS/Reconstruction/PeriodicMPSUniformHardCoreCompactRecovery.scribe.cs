using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformHardCoreCompactRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformHardCoreCompactRecovery";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local reconstruction against the whole compact closure",
        H("Local reconstruction against the whole compact closure"),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhardcorecompactrecovery-exists-generic-compact-reconstruction"),
                DeclarationHandle.Create(Module + ".exists_generic_compact_reconstruction"),
                H("Local reconstruction against the whole compact closure"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Near the hard-core witness for every ring length at least seven, a relatively open dense set of targets has singleton fibers even in the compact closure. A compact chart neighborhood contains every competitor whose observation lies in the guard."))),
                DescribeRole.Theorem))));
}
