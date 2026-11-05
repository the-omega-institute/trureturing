using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianTraceBilinearDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Bilinear Trace Exchange",
        H("Original Gaussian Bilinear Trace Exchange"),
        Blocks(
            Paragraph(Text("The literal finite matrix moment equals its unconjugated contraction on the original infinite l2 carrier. Absolutely convergent odd-power series give the difference of the genuine signed inverses. Uniform control of the weighted source and both inverses yields compact-uniform scalar derivative convergence and differentiates the actual infinite cutoff limit. The current operator differentiation owner supplies the negative weighted scalar, and the weighted resolvent owner supplies the positive scalar; together they give the radial logarithmic derivative in terms of the existing period F.")),
            Paragraph(Text("These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.")),
            Describe.Lean(
                DescribeId.Create("finite-trace-moment-eq-actual-cutoff-bilinear"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear.finiteTraceMoment_eq_actual_cutoff_bilinear"),
                H("finiteTraceMoment_eq_actual_cutoff_bilinear"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every N, every natural power including zero and every real parameter, the finite matrix moment equals its literal unconjugated l2 cutoff contraction."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-odd-moment-series-eq-signed-inverse-difference"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear.actual_odd_moment_series_eq_signed_inverse_difference"),
                H("actual_odd_moment_series_eq_signed_inverse_difference"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For interior radial parameters, the odd scalar series and both signed inverse contractions converge absolutely, and the odd sum equals one half of the difference of the two actual inverse contractions."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compact-uniform-scalar-derivatives-and-final-exchange"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear.compact_uniform_scalar_derivatives_and_final_exchange"),
                H("compact_uniform_scalar_derivatives_and_final_exchange"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On each interior open radial interval with enclosing radius below one, the finite logarithm derivatives converge uniformly to the two actual bilinear inverse contractions, and their limit differentiates the infinite logarithm."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det-has-deriv-at-bilinear-resolvent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear.gaussianLogDet_hasDerivAt_bilinear_resolvent"),
                H("gaussianLogDet_hasDerivAt_bilinear_resolvent"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, the actual infinite logarithm at sqrt r has derivative minus one over two r times the difference of the two unconjugated weighted inverse scalars."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-log-det-has-deriv-at-period"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianTraceBilinear.gaussianLogDet_hasDerivAt_period"),
                H("gaussianLogDet_hasDerivAt_period"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real r strictly between zero and one, the derivative of the original infinite logarithm at sqrt r equals deriv F r divided by F r minus one over four times one minus r, embedded into the complex numbers."))), DescribeRole.Theorem))));
}
