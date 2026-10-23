using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.IncompleteBetaShape;

internal sealed class MixtureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Beta mixtures for coefficient convolutions with two first parameters.",
        H("Coefficient convolution as a beta mixture mean"), Blocks(
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-convolution"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution"),
                H("Coefficient convolution"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive real p, q and b, the nth convolution is the sum of c_k(p,b)c_(n-k)(q,b) for k from zero through n."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-mixture-density"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureDensity"),
                H("Uniform mixture density"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The density is the uniform average, with weight 1/(n+1), of the beta densities with shapes p+k+1 and q+n-k+1. Their common total shape is p+q+n+2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-mixture-factor"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.mixtureFactor"),
                H("Common prefactor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The prefactor K(c,n,b) is (n+1)Gamma(c+n+2b) divided by Gamma(b)^2 Gamma(c+n+2). Its first parameter is the sum c=p+q."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-convolution-mixture-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_mixtureMean"),
                H("Beta mixture representation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive p, q and b, the coefficient convolution equals K(p+q,n,b) times the integral of [y(1-y)]^(b-1) against the uniform beta mixture density on the unit interval. Each summand is evaluated by the beta integral with shapes p+b+k and q+b+n-k. Positivity of the parameters gives integrability even when the power weight is unbounded at the endpoints."))),
                DescribeRole.Theorem))));
}
