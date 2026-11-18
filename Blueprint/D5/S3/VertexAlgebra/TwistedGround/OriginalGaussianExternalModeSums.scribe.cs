using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalModeSumsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Frequency Moment Generators", H("Signed Frequency Moment Generators"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("sourcemoment-generators"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators"),
                H("sourceMoment_generators"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Both original U mode series are differentiated A generators on norm(u)+norm(x)<1. The positive sum equals u(1-u) Mplus derivative +(1-3u) Mplus/2 - Aminus(0)/2. Multiplying the negative sum by u gives u(1-u) Mminus derivative -(u+1) Mminus/2 + Aminus(0)/2. The actual input-zero term is retained in both equations."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcemoment-generators-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.sourceMoment_generators_explicit"),
                H("sourceMoment_generators_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the same joint disk, the positive U sum is Mplus times (1-2u+(1-x)u squared)/(2(1-(1-x)u)) minus Aminus(0)/2. The negative U sum multiplied by u is Mminus times (u(1-u)/(2(1-x-u))-1/2) plus Aminus(0)/2. The mode derivative follows from normal convergence and the actual algebraic generator square."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mode-derivative"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative"),
                H("mode_derivative"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign on norm(u)+norm(x)<1, the differentiated actual sourceAmplitude mode series has sum equal to the first external-variable derivative of sourceMode, and sourceMode is complex differentiable there."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mode-factors-ne-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_factors_ne_zero"),
                H("mode_factors_ne_zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the same joint disk the factors 1-u, 1-(1-x)u and 1-x-u are all nonzero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("mode-derivative-explicit"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalModeSums.mode_derivative_explicit"),
                H("mode_derivative_explicit"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign on the same disk, with a=1 and b=1-x for the positive sign and a=1-x and b=1 for the negative sign, the external-variable derivative of the actual sourceMode equals sourceMode times [1/(2(1-u))+b/(2(a-bu))]."))), DescribeRole.Theorem))));
}
