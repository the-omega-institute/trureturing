using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformSpectralRadicalAlgebraDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformSpectralRadicalAlgebra";
    private const string Title = "Radical presentation of the split determinant chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformspectralradicalalgebra"),
                DeclarationHandle.Create(Module + ".coordinateEquivRadicalAlgebra"),
                H("Equivalent coordinate and radical algebras"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The split determinant chart is isomorphic over its coefficient ring to the algebra obtained by adjoining the two indicated square roots."))),
                DescribeRole.Definition))));
}
