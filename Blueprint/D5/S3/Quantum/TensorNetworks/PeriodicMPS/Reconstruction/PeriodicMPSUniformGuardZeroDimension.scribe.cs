using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class PeriodicMPSUniformGuardZeroDimensionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/PeriodicMPSUniformGuardZeroDimension";
    private const string Title = "Hausdorff dimension of the native periodic MPS guard-zero locus";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("uniform-native-guard-identity"),
                DeclarationHandle.Create(Module + ".nativeGuard_eq_physicalGuard"),
                H("The spectral guard in native coordinates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pullback of the ambient spectral-localization guard is the physical guard as a complex multivariate polynomial in the five Cartesian slice coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-native-guard-nonzero-mixed-dimension"),
                DeclarationHandle.Create(Module + ".dimH_nativeGuard_zero_of_mixedTrace_ne_zero"),
                H("Dimension with nonzero mixed trace"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In the nonzero aligned mixed-trace sector the zero locus of the native guard has real Hausdorff dimension at most six."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-native-guard-zero-dimension"),
                DeclarationHandle.Create(Module + ".dimH_nativeGuard_zero"),
                H("Dimension of the full guard-zero locus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The full native guard-zero locus has real Hausdorff dimension at most six in the ambient space of ordinary trace-one parameters. The proof takes the union of the nonzero mixed-trace bound and the six-dimensional zero mixed-trace sector."))),
                DescribeRole.Theorem))));
}
