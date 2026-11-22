using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformGraphRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGraphRecovery";
    private const string Title = "Uniform two-site recovery from a critical-locus dimension bound";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsuniformgraphrecovery-result"),
            DeclarationHandle.Create(Module + ".generic_twoSite_recovery"),
            H(Title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Fix m with n = 2 + m ≥ 7. If the ordinary trace-one chart's critical coordinate set for the normalized adjacent-pair observation has real Hausdorff dimension at most six, there is a relatively Euclidean-open dense subset of the compact closure of the actual periodic binary bond-two projector image. Each target in that subset is an actual projector. Every competitor in the compact closure with the same normalized adjacent-pair marginal equals the target projector. Thus actual unit-mass competitors agree up to unit phase. Relative openness and density use the real Euclidean topology. The proof combines the compact graph boundary bound, the hard-core singleton neighborhood, and compact regular-fiber continuation."))),
            DescribeRole.Theorem))));
}
