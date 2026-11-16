using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class OriginalGaussianExternalGeneratorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed Generators of the Literal Source Amplitudes",
        H("Signed Generators of the Literal Source Amplitudes"),
        Blocks(
            Paragraph(Text("Absolute reindexing sums the actual A coefficients over the external modes. The positive generator is (1-u)^(-1) times the central binomial series at -xu/(1-u); the negative generator uses x/(1-u). The binomial power series fixes the analytic branches at the origin. The all-mode J/T kernel identification, removable J diagonal and singular-ODE coefficient uniqueness remain separate unproved obligations.")),
            Describe.Lean(
                DescribeId.Create("centralgenerating"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.centralGenerating"),
                H("centralGenerating"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the literal centralWeight power series in a complex argument."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-mode-hassum"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_mode_hasSum"),
                H("sourceAmplitude_mode_hasSum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and norm(u)+norm(x)<1, the complete A mode sum has the value obtained by summing its absolutely convergent coefficient double series in the reversed order."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-positive-generator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_positive_generator"),
                H("sourceAmplitude_positive_generator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On norm(u)+norm(x)<1, the positive A mode series sums to centralGenerating(-xu/(1-u))/(1-u)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-negative-generator"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_negative_generator"),
                H("sourceAmplitude_negative_generator"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On norm(u)+norm(x)<1, the negative A mode series sums to centralGenerating(x/(1-u))/(1-u)."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourceamplitude-generators"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceAmplitude_generators"),
                H("sourceAmplitude_generators"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On norm(u)+norm(x)<1, both complete signed A mode series equal their analytic binomial branches: positive (1-u)^(-1)(1+xu/(1-u))^(-1/2), negative (1-u)^(-1)(1-x/(1-u))^(-1/2). No value of a singular J quotient is assigned at the diagonal."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sourcemode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode"),
                H("sourceMode"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and complex u,x, sourceMode is the tsum of the actual sourceAmplitude at each natural external mode times u to that mode."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("sourcemode-square"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.sourceMode_square"),
                H("sourceMode_square"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On norm(u)+norm(x)<1, the actual positive sourceMode square is 1/((1-u)(1-(1-x)u)); the negative square is 1/((1-u)(1-x-u)). The previously evaluated binomial branches fix which square root germ occurs."))), DescribeRole.Theorem),

            Describe.Lean(
                DescribeId.Create("amplitude-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/OriginalGaussianExternalGenerators.amplitudeTerm"),
                H("amplitudeTerm"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either label and complex u,x, this is the actual coefficient product c_n (-1)^n choose(alpha(p)-1/2,n) x^n u^p on the pair (p,n). It is consumed by the absolute mode-reindexing theorem."))), DescribeRole.Definition))));
}
