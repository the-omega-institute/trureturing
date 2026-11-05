using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class OriginalGaussianIntegralBudgetsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original localization budgets on their exact domains.",
        H("The original localization budgets on their exact domains"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("original-gaussian-central-budget"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/OriginalGaussianIntegralBudgets.central_original"),
                H("The original localization budgets on their exact domains"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("The literal density g(m,M,y)=exp(-(y-M)^2/(4*m))/sqrt(4*pi*m) has mean M and variance 2*m for m>0. The existing GaussianComplexMoments.density_monomial_integrable at mean zero and variance 2*m supplies every polynomial degree; taking the real part and translating by M pays g_power_integrable. No second arbitrary-mean density integrability proof is ported.")),
                Paragraph(Text("The existing CountableGaussianQuadraticFourthMoment.centralMoment_two_mul at n=1,2 supplies the scalar Gaussian moments. pdf_moments transports those probability integrals to the actual Lebesgue density with integral_gaussianReal_eq_integral_smul. Thus the central second and fourth moments are 2*m and 12*m^2. The resulting degree-four polynomial integral is A+2*m*B+12*m^2*C, with integrability proved before linearity.")),
                Paragraph(Text("The scalar even-moment proof belongs to RemyDegenne/brownian-motion, BrownianMotion/Gaussian/Moment.lean, centralMoment_two_mul_gaussianReal, commit 0d5b6eb928e616d3b1f774ad7d233c167d9f42c9, under Apache-2.0. Its existing project supplier retains the attribution and license; this module reuses that supplier rather than reproducing the proof.")),
                Paragraph(Text("Completing the square gives exp(t*y)*gaussianDensity(m,y)=exp(m*t^2+16*m*t)*g(m,16*m+2*m*t,y). Splitting the Gaussian exponent gives g(m,M,y)=sqrt(2)*exp(-(y-M)^2/(8*m))*g(2*m,M,y). If (y-M)^2>=8*c*m^2, this is at most (3/2)*exp(-c*m)*g(2*m,M,y). OriginalGaussianIntegralBudgets consumes these transports and estimates on their exact domains.")),
                Paragraph(Text("These are consumed proof-support results. Their algebraic identities, moments and integrability adapters are not represented as independent mathematical novelty or a standalone admission witness.")),
                Paragraph(Text("For m>=1 and gamma>10, b(y)=(4*y+11)*exp(y/2). The exact central positive integral over (0,infinity) obeys integral b*V<=300*m*(gamma+10)^2*exp(33*m/4). Tilting moves the normalized Gaussian center to 17*m. A positive quartic majorant integrates to 2*exp(33*m/4)*(85*m*(gamma^2+2)+93), using the attributed existing second and fourth moments.")),
                Paragraph(Text("On [0,infinity) outside the CLOSED interval [4*m,28*m], tilting by exp(y) moves the center to 18*m. The exterior has squared distance at least 100*m^2 from that center. Splitting the exponent supplies exp(-25*m/2), which combines with exp(17*m) to give exp(9*m/2). The exact exterior integral of abs(Re(H))*V is at most 12*(gamma+10)^2*exp(9*m/2).")),
                Paragraph(Text("On the ENTIRE negative axis, squared distance from 16*m is at least 256*m^2. The Gaussian split supplies exp(-32*m), and the integral of abs(Re(H))*V is at most 8*(gamma+10)^2*exp(-32*m). Global product integrability is proved before these restrictions; it includes the sign change of b on the negative axis.")),
                Paragraph(Text("The complement identity is [4*m,28*m]^c=([0,infinity)\\[4*m,28*m]) union (-infinity,0), with disjoint pieces. Both closed endpoints remain central. The change from [0,infinity) to (0,infinity) uses only the zero-measure singleton endpoint. OriginalPositiveUPeak consumes all three budgets and these exact domain facts together with the separate full signed-HV budget."))),
                DescribeRole.Theorem))));
}
