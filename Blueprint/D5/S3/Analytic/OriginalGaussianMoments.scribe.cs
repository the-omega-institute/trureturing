using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic;

internal sealed class OriginalGaussianMomentsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original Gaussian density transport and integral estimates.",
        H("Original Gaussian density transport and integral estimates"),
        Blocks(
                Paragraph(Text("The literal density g(m,M,y)=exp(-(y-M)^2/(4*m))/sqrt(4*pi*m) has mean M and variance 2*m for m>0. The existing GaussianComplexMoments.density_monomial_integrable at mean zero and variance 2*m supplies every polynomial degree; taking the real part and translating by M pays g_power_integrable. No second arbitrary-mean density integrability proof is ported.")),
                Paragraph(Text("The existing CountableGaussianQuadraticFourthMoment.centralMoment_two_mul at n=1,2 supplies the scalar Gaussian moments. pdf_moments transports those probability integrals to the actual Lebesgue density with integral_gaussianReal_eq_integral_smul. Thus the central second and fourth moments are 2*m and 12*m^2. The resulting degree-four polynomial integral is A+2*m*B+12*m^2*C, with integrability proved before linearity.")),
                Paragraph(Text("The scalar even-moment proof belongs to RemyDegenne/brownian-motion, BrownianMotion/Gaussian/Moment.lean, centralMoment_two_mul_gaussianReal, commit 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9, under Apache-2.0. Its existing project supplier retains the attribution and license; this module reuses that supplier rather than reproducing the proof.")),
                Paragraph(Text("Completing the square gives exp(t*y)*gaussianDensity(m,y)=exp(m*t^2+16*m*t)*g(m,16*m+2*m*t,y). Splitting the Gaussian exponent gives g(m,M,y)=sqrt(2)*exp(-(y-M)^2/(8*m))*g(2*m,M,y). If (y-M)^2>=8*c*m^2, this is at most (3/2)*exp(-c*m)*g(2*m,M,y). OriginalGaussianIntegralBudgets consumes these transports and estimates on their exact domains.")),
                Paragraph(Text("These are consumed proof-support results. Their algebraic identities, moments and integrability adapters are not represented as independent mathematical novelty or a standalone admission witness.")))));
}
