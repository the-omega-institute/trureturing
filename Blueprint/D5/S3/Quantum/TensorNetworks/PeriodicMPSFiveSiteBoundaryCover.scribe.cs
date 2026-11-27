using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class PeriodicMPSFiveSiteBoundaryCoverDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPSFiveSiteBoundaryCover";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Five-site observations at the boundary",
        H("Five-site observations at the boundary"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsfivesiteboundarycover-result"),
            DeclarationHandle.Create(Module + ".real_boundary_observation_cover"),
            H("Five-site observations at the boundary"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "Finitely many differentiable maps from six real coordinates cover the observations outside the ordinary trace chart."))),
            DescribeRole.Theorem))));
}
