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
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-affine-mixture"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.mixture_eq_affine"),
                H("Affine mixture identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive p and q, a measurable real test function integrable against the shifted beta mixture has the same mean under the affine variable s v + (1-s)u. Here v has beta shapes p,q, s has beta shapes p+q,n+2, and u is uniform on the unit interval. The joint density normalizer is Gamma(p)Gamma(q)Gamma(n+2)/Gamma(p+q+n+2).")),
                    Paragraph(Text("The triangle coordinate integral identity, with x=s v and z=s(1-v) and Jacobian s, is restricted to the output rectangle. At fixed output y its domain becomes the rectangle 0<x<y and 0<z<1-y. Expanding (1-x-z)^n into the n+1 terms ((y-x)+(1-y-z))^n and evaluating each beta integral produces the uniform shifted beta density. Nonnegative integration establishes the measure identity, and integrability transfers it to real test functions."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("incomplete-beta-shape-convolution-kernel-mean"),
                DeclarationHandle.Create("D5/S3/Analytic/IncompleteBetaShape/Mixture.convolution_eq_betaMean_H"),
                H("Beta mean of the averaged kernel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The coefficient convolution at p,q equals K(p+q,n,b) times the beta mean of H(p+q,n,b), with mean shape (p+q)/2 and signed imbalance (p-q)/2. Boundedness of H controls the outer beta integral, and the nonnegative affine identity transfers this finiteness to the weighted mixture. Thus the identity includes the singular endpoint regime 0<b<1. The common prefactor and kernel depend on p,q only through their sum, allowing strict comparison by imbalance."))),
                DescribeRole.Theorem))));
}
