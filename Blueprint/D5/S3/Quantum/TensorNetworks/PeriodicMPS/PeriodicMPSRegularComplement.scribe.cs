using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS;

internal sealed class PeriodicMPSRegularComplementDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/PeriodicMPSRegularComplement";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complements of lower-dimensional differentiable covers",
        H("Complements of lower-dimensional differentiable covers"),
        Blocks(Describe.Lean(DescribeId.Create("periodicmpsregularcomplement-result"),
            DeclarationHandle.Create(Module + ".isPathConnected_compl_of_smooth_cover"),
            H("Complements of lower-dimensional differentiable covers"), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                "In the stated dimension range, a countable differentiable cover of an excluded set leaves a path-connected complement."))),
            DescribeRole.Theorem))));
}
