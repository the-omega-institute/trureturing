using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformVerticalAmbientAlgebraDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformVerticalAmbientAlgebra";
    private const string Title = "Specialization and generic fields of the ordered chart";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformverticalambientalgebra"),
                DeclarationHandle.Create(Module + ".genericChart_isField"),
                H("Generic field after coefficient specialization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If two is nonzero in the target field and the image of c minus b squared is nonzero, the specialized radical algebra over the rational function field of the two free parameters is a field."))),
                DescribeRole.Theorem))));
}
