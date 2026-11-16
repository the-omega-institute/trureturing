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
                DescribeId.Create("derivative-shifted-geometric"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.derivative_shifted_geometric"),
                H("derivative_shifted_geometric"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every natural polynomial coordinate weight is summable against a positive geometric ratio strictly below one. This bound controls the differentiated source and central-binomial series."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-coefficient"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceCoefficient"),
                H("sourceCoefficient"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The single-coordinate coefficient of the original source family, including its inverse frequency square root."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-family-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamilyTerm"),
                H("sourceFamilyTerm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The natural coordinate weight and complex power multiply the original single-coordinate coefficient."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("source-family-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_summable"),
                H("sourceFamily_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural coordinate weight and every complex parameter of norm less than one, the original source-family terms are norm-absolutely summable."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-family-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_apply"),
                H("sourceFamily_apply"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every coordinate of the original source family equals the displayed half-binomial coefficient, coordinate weight and complex power divided by the frequency square root."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-family-zero-eq-source"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_zero_eq_source"),
                H("sourceFamily_zero_eq_source"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At the square root of any real parameter in the half-open unit interval, the zeroth source family is the original source vector."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-column-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumnDerivative"),
                H("radialColumnDerivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The real radial derivative of the original source column is the complex derivative scaled by the derivative of the square root."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radial-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialNormalization"),
                H("radialNormalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The scalar normalization is the reciprocal of the real period times the square root of one minus the radial parameter."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radial-column-derivative-scaled"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_column_derivative_scaled"),
                H("radial_column_derivative_scaled"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the open real unit interval, the radial column derivative multiplied by the radial parameter is one half of the normalization times the original resolvent applied to the weighted source."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("negative-weighted-scalar"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.bilinear_negative_resolvent_weighted_scalar"),
                H("bilinear_negative_resolvent_weighted_scalar"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, the weighted source paired with the actual one-minus resolvent column is absolutely summable and equals 3r/(4(1-r)) minus 2r times the derivative of F divided by F, embedded into the complex numbers."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radialsourcefamily"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialSourceFamily"),
                H("radialSourceFamily"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original source family evaluated at the complex embedding of the real square root, with the natural frequency weight unchanged."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("radialcolumn"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radialColumn"),
                H("radialColumn"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual source resolvent column evaluated at the complex embedding of the real square root."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-sourcefamily"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_sourceFamily"),
                H("hasDerivAt_radial_sourceFamily"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural j and every real 0<r<1, the jth radial source family has derivative the next weighted source divided by 2r."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hasderivat-radial-column"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.hasDerivAt_radial_column"),
                H("hasDerivAt_radial_column"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 0<r<1, the actual radial column has derivative radialColumnDerivative r."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcebilinearfunctional"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional"),
                H("sourceBilinearFunctional"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original ordinary complex bilinear pairing is innerSL with star on the first vector."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourcebilinearfunctional-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_apply"),
                H("sourceBilinearFunctional_apply"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For all square-summable complex vectors w and x, the original bilinear functional equals the sum of their coordinate products."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcebilinearfunctional-smul-left"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceBilinearFunctional_smul_left"),
                H("sourceBilinearFunctional_smul_left"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original bilinear functional is complex linear in its first argument."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcefamily-one-eq-weightedsource"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.sourceFamily_one_eq_weightedSource"),
                H("sourceFamily_one_eq_weightedSource"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 0<=r<1, the first source family at sqrt(r) is the literal frequency-weighted original source."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("radial-pair-normalization"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianDifferentiation.radial_pair_normalization"),
                H("radial_pair_normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real 0<r<1, one plus the ordinary bilinear pairing of the first radial source family with the radial column is the complex embedding of radialNormalization r."))), DescribeRole.Theorem))));
}
