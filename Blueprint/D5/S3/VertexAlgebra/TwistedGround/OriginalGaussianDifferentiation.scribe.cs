using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianDifferentiationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Operator and Resolvent Differentiation",
        H("Original Gaussian Operator and Resolvent Differentiation"),
        Blocks(
            Paragraph(Text("The carrier, literal signed operator, original source and signed Neumann column are imported from their existing owners. The derivative owner keeps the same complex square-summable carrier and uses norm-absolutely convergent rank-one and coordinate-weighted series on the open unit disk.")),
            Paragraph(Text("The operator derivative is obtained by differentiating the actual rank-one series under a polynomial-geometric majorant. A general coordinate-weighted source family is differentiated in the norm of the original carrier, and the Neumann inverse is differentiated through its norm-controlled one-minus operator unit. The original column derivative is the derivative of the actual inverse column, with no determinant or trace interchange.")),
            Paragraph(Text("On the real radial interval, the frequency-weighted source supplies the literal rank-one identity for the radial operator derivative. The negative-sign resolvent moment is then computed from the differentiated normalized column and the existing positive weighted column pair. The result is a coefficient-model identity for the actual inverse of one minus the operator.")),
            Paragraph(Text("These results establish no determinant derivative exchange, determinant-period identity, endpoint asymptotic, physical Gaussian realization, vertex-operator-algebra construction, fusion or anomaly statement, string theory, or AdS/CFT realization.")),
            Describe.Lean(
                DescribeId.Create("operator-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.operatorDerivative"),
                H("operatorDerivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The norm-summable termwise derivative of the literal signed rank-one operator series on the complex unit disk."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("operator-has-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_operator"),
                H("hasDerivAt_operator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every complex z with norm less than one, the original operator has the displayed operator-norm derivative operatorDerivative z."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-family-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_sourceFamily"),
                H("hasDerivAt_sourceFamily"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every natural coordinate weight j gives a norm-differentiable source family; its derivative raises the coordinate weight by one and lowers the complex power by one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("resolvent-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_resolvent"),
                H("hasDerivAt_resolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual Neumann inverse of one minus the literal operator has derivative resolvent z multiplied on both sides of operatorDerivative z."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("column-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_columnSeries"),
                H("hasDerivAt_columnSeries"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original inverse column, formed from the actual source family and signed resolvent, has the derivative obtained by the product rule for the resolvent and source."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-rank-one"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_operator_derivative_rankOne"),
                H("radial_operator_derivative_rankOne"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("After multiplying by r, the radial operator derivative is one half of the rank-one map built from the actual weighted source and its unconjugated bilinear functional."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-weighted-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar"),
                H("bilinear_negative_resolvent_weighted_scalar"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, the weighted source paired with the actual one-minus resolvent column is absolutely summable and equals 3r/(4(1-r)) minus 2r times the derivative of F divided by F, embedded into the complex numbers."))), DescribeRole.Theorem))));
}
