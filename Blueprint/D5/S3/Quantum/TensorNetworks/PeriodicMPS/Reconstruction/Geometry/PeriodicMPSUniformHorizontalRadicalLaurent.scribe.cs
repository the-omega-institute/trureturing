using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Geometry;

internal sealed class PeriodicMPSUniformHorizontalRadicalLaurentDocument : IScribeDocumentDefinition
{
    private const string Title = "Spectral degree under Laurent coefficient extraction";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalradicallaurent-shiftedlaurent-totaldegree-le"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.shiftedLaurent_totalDegree_le"),
                H("Monomial clearing preserves the coefficient bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The clearing factor translates Laurent indices. Each extracted spectral polynomial has degree bounded by the original degree."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontalradicallaurent-spectralcoeffafterspecialization-totaldegree-le"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Geometry/PeriodicMPSUniformHorizontalRadicalLaurent.spectralCoeffAfterSpecialization_totalDegree_le"),
                H("Degree survives axis specialization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After fixing either unit parameter, taking a remaining Laurent coefficient can only remove spectral monomials."))),
                DescribeRole.Theorem))));
}
