using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorSameRLeftCovarianceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "LatticeSectorSameRLeftCovariance", H("LatticeSectorSameRLeftCovariance"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorsamerleftcovariance-middlepolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSameRLeftCovariance.middlePolynomial"),
                H("middlePolynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The middlePolynomial coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorsamerleftcovariance-finalpolynomial"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSameRLeftCovariance.finalPolynomial"),
                H("finalPolynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finalPolynomial coefficient construction uses the displayed signed indices and finite polynomial fibers, with exactly the assumptions of its Lean statement."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorsamerleftcovariance-actual-three-field-same-r-left-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Sectors/LatticeSectorSameRLeftCovariance.actual_three_field_same_R_left_covariance"),
                H("actual_three_field_same_R_left_covariance"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original all-integer Borcherds identity and common-middle equality give the finite action of the literal final polynomial on the actual left-nested channel. Actual original-state truncation removes the temporary extra multiplier, retaining the original k, a, P and six signed laws."))), DescribeRole.Theorem))));
}
