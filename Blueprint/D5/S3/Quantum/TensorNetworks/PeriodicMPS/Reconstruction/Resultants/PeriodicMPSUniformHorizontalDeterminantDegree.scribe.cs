using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction.Resultants;

internal sealed class PeriodicMPSUniformHorizontalDeterminantDegreeDocument : IScribeDocumentDefinition
{
    private const string Title = "Spectral degree of cofactor and resultant determinants";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontaldeterminantdegree-det-totaldegree-le-column-sum"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformHorizontalDeterminantDegree.det_totalDegree_le_column_sum"),
                H("Determinant degree is bounded by the column budgets"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each term of the determinant uses one entry from each column."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("periodicmpsuniformhorizontaldeterminantdegree-resultant-totaldegree-le"),
                DeclarationHandle.Create("D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/Resultants/PeriodicMPSUniformHorizontalDeterminantDegree.resultant_totalDegree_le"),
                H("Fixed-degree Sylvester bound"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two groups of columns in the Sylvester matrix contribute their respective degree budgets."))),
                DescribeRole.Theorem))));
}
