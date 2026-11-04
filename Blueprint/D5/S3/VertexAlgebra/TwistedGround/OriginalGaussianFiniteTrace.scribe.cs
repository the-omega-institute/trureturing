using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianFiniteTraceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian Finite Trace Differentiation",
        H("Original Gaussian Finite Trace Differentiation"),
        Blocks(
            Paragraph(Text("Entrywise matrix differentiation keeps the full noncommutative power differential until cyclicity is applied to the trace. The original weighted finite moments have a dimension-independent bound from an absolutely summable weighted-source majorant. The finite trace-log derivative is obtained by a derivative M-test on each interior radial interval.")),
            Paragraph(Text("These are analytic identities for the original coefficient model on its infinite carrier. Physical vertex operator algebras, conformal field theory, anomaly and fusion structures, string theory and AdS/CFT realization remain open.")),
            Describe.Lean(
                DescribeId.Create("trace-finite-weight"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceFiniteWeight"),
                H("traceFiniteWeight"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original source coordinate multiplied by its positive physical frequency on the finite section."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-trace-moment"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment"),
                H("finiteTraceMoment"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite matrix-power moment with two original weighted source factors and no complex conjugation."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-weight-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound"),
                H("traceWeightBound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A polynomial-geometric coordinate bound at the enclosing radial radius."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-weight-mass"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightMass"),
                H("traceWeightMass"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The sum of the nonnegative coordinate majorant."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("trace-weight-bound-summable"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightBound_summable"),
                H("traceWeightBound_summable"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The weighted coordinate majorant is summable for every nonnegative radius below one."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("trace-weight-value-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.traceWeightValue_bound"),
                H("traceWeightValue_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each original signed weighted coordinate is bounded by the enclosing-radius majorant."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-trace-moment-bound"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteTraceMoment_bound"),
                H("finiteTraceMoment_bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite power moment is bounded by the square of the majorant mass times the radial power, independently of the section dimension."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-log-has-deriv-at-trace-moments"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianFiniteTrace.finiteLog_hasDerivAt_traceMoments"),
                H("finiteLog_hasDerivAt_traceMoments"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite section and real r strictly between zero and one, the actual finite logarithm at sqrt r has derivative minus one over r times the sum of its odd weighted moments."))), DescribeRole.Theorem))));
}
