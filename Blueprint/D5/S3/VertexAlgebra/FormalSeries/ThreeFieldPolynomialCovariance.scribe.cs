using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.FormalSeries;

internal sealed class ThreeFieldPolynomialCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "ThreeFieldPolynomialCovariance", H("ThreeFieldPolynomialCovariance"), Blocks(
            Describe.Lean(DescribeId.Create("threefieldpolynomialcovariance-finite-inner-recoupling"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/FormalSeries/ThreeFieldPolynomialCovariance.finite_inner_recoupling"),
                H("finite_inner_recoupling"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite polynomial expansion regroups the original cleared inner channel into fixed middle-mode product slices without an infinite interchange."))), DescribeRole.Theorem))));
}
