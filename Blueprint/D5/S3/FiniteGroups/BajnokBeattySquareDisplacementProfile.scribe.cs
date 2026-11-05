using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementProfileDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Squared displacement selects Perron order q^2; one finite Taylor estimate gives a uniform ray slope, its unique Perron crossing, and the exact scaling limits of both correction coefficients.",
        H("Square-displacement profiles and coefficient scaling"),
        Blocks(
            Paragraph(Text(
                "For every natural q, put Q=(q as a real number), nu=q^2, beta_q=dbonacciPerronRoot(nu), and sigma_q=log(beta_q). Define G_q(s)=exp(s)+exp(-Q^2*s) for every real s. The total real coefficients are d_q=((Q^2+1)*sigma_q/(6*Q*(Q^2-1)))*(((Q^4+1)*beta_q-2*Q^4)/((Q^2+1)*beta_q-2*Q^2)) and b_q=d_q-1/(2*Q). These definitions include the finitely many q<3; the limits below have domain all natural numbers.")),
            Describe.Lean(
                DescribeId.Create("square-displacement-profile-result"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/BajnokBeattySquareDisplacementProfile.square_displacement_profile"),
                H("Uniform slope, unique ray root, and both scaling limits"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural q>=3 and every real s>=2/3, deriv(G_q)(s)>161/90. For every such q and all real a,b with 2/3<=a<=b, (161/90)*(b-a)<=G_q(b)-G_q(a); if a<b the inequality is strict. When a=b both sides are zero.")),
                    Paragraph(Text(
                        "For every natural q>=3 and every real s>=2/3, G_q(s)=2 if and only if s=sigma_q. Thus uniqueness is on the ray [2/3,infinity). The additional root G_q(0)=2 is outside that ray.")),
                    Paragraph(Text(
                        "As q tends to infinity through all natural numbers, Q*d_q tends to log(2)/6, and Q*b_q tends to log(2)/6-1/2. Here d_q and b_q are exactly the total coefficients defined above, with no restriction of the limit domain to odd q or to a subtype of q>=3.")),
                    Paragraph(Text(
                        "The common estimate holds for every real v>=9. The finite exponential sum through degree four gives exp(2v/3)>(2v/3)^3/6+(2v/3)^4/24=v^2*(4v/81+2v^2/243). Retaining this unsimplified factor yields 0<v^2*exp(-2v/3)<243/(2v*(v+6))<=9/10. For every s>=2/3 the same rational upper bound holds for v^2*exp(-v*s). Consequently v*exp(-v*s)<1/10, while exp(s)>=1+s+s^2/2>=17/9. Differentiation gives G_q'(s)=exp(s)-nu*exp(-nu*s)>161/90. The mean value theorem gives the strict secants and their non-strict endpoint extension.")),
                    Paragraph(Text(
                        "Monotonicity of the existing Perron family and the order-nine logarithm bound give 2/3<sigma_q<log(2) when q>=3. Its reciprocal equation gives w_q=exp(-nu*sigma_q)=beta_q^(-nu)=2-beta_q and G_q(sigma_q)=2. Strict secants therefore identify every ray root with sigma_q. The same finite Taylor estimate supplies the sign analysis: nu^2*w_q<9/10<beta_q makes beta_q-nu^2*w_q positive, and G_q'(sigma_q)=beta_q-nu*w_q>161/90 makes the denominator positive.")),
                    Paragraph(Text(
                        "For the limits, the same bound 0<nu^2*w_q<243/(2nu*(nu+6)) tends to zero; also 0<nu*w_q<=nu^2*w_q. The existing Perron limit composed with q mapped to q^2 gives beta_q tending to 2, and logarithm continuity gives sigma_q tending to log(2). Hence (beta_q-nu^2*w_q)/(beta_q-nu*w_q) tends to 1 with limiting denominator 2, and (nu+1)/(nu-1)=1+2/(nu-1) tends to 1. For q>=3 exact algebra gives Q*d_q=(sigma_q/6)*((nu+1)/(nu-1))*((beta_q-nu^2*w_q)/(beta_q-nu*w_q)) and Q*b_q=Q*d_q-1/2. These eventual identities preserve the full natural limit domain.")),
                    Paragraph(Text(
                        "Since log(2)<1, the limit log(2)/6-1/2 is strictly negative. This is a quantitative structural consequence of squared displacement: subtracting the geometric half-step dominates the rescaled positive Perron contribution. This result does not establish a general-q finite-count error envelope, an integer threshold law, exact rounding, infinitely many counterexamples, or literature novelty."))),
                DescribeRole.Theorem)
        )));
}
