using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.GaussianLocalization;

internal sealed class CompleteActualSignedGaussianExchangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The signed Gaussian transform over all actual occurrences.",
        H("The signed Gaussian transform over all actual occurrences"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-signed-k-exchange"),
                DeclarationHandle.Create("D5/S3/Arith/Robin/GaussianLocalization/CompleteActualSignedGaussianExchange.actual_signed_K_exchange"),
                H("The signed Gaussian transform over all actual occurrences"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                Paragraph(Text("For m>0, write u=(y-16*m)/(2*m), g=exp(-(y-16*m)^2/(4*m))/sqrt(4*pi*m), P=(u+i*gamma)*(u+i*gamma-1)-1/(2*m), W=-exp(-i*gamma*y)*P*g, K=Re(W) and V=2*(u^2+gamma^2+1)*g. The literal complete H sums exp(y*rho)/(rho*(1-rho)) over every actual occurrence.")),
                Paragraph(Text("The current arbitrary-mean complex Gaussian moments of degrees zero, one and two give integral exp(rho*y)*W(y)=-rho*(rho-1)*exp(m*(rho-i*gamma)^2+16*m*(rho-i*gamma)). The two minus signs in 1/(rho*(1-rho)) and this transform cancel, giving a POSITIVE shifted-exponential sum. The V transform retains its full complex reciprocal coefficient and factor two.")),
                Paragraph(Text("Polynomial Gaussian integrability and its unit real shift pay the weight exp(max(y,0)). The existing actual_complete_H_package directly supplies the whole-line signed exchanges from its paid absolute domination; no second actual occurrence exchange proof is needed. For m>=1 the kernel obeys abs(K)<=V and K+V>=0. The current actual_complete_H_package supplies the zero imaginary part of H. Passing to real parts only after product integrability yields integral Re(H)*K=Re(sum exp(m*(rho-i*gamma)^2+16*m*(rho-i*gamma))).")),
                Paragraph(Text("The full V response is consumed by ActualGaussianEnvelopeMassBudget; the K response and product-integrability statements are consumed by OriginalPositiveUPeak and OriginalGaussianIntegralBudgets. The removed W/V tilt-integrability wrappers follow directly from quadraticAt_integrable at rho-i*gamma and envelopeAt_integrable at rho. The K tilt norm is bounded by the W tilt norm using abs(Re(W))<=norm(W); likewise the weighted K norm is bounded by the weighted W norm for every m>0. The removed complex H*K integrability follows from the same H-growth majorant, and the V real-exchange follows by integral_re and extracting its factor two. Restricting the existing H-product integrability and the two tilted integrability facts recovers all integrability components of the old W_exchange_on and V_exchange_on; For a measurable set s, apply the same existing package to the indicator of the continuous weight w. Weighted integrability restricts to s, and integral_indicator gives the exact signed restricted sum. This recovers the old W_exchange_on and V_exchange_on without retained specialized wrappers or a duplicate exchange module. More generally, a(k)=1/(rho(k)*(1-rho(k))) and the strip give norm(a(k)*exp(y*rho(k))*w(y))<=norm(a(k))*exp(max(y,0))*norm(w(y)). Summability of norm(a(k)) and restricted integrability of this common weight give per-term integrability, integrability of the sum of norms and HasSum of the norm integrals by dominated convergence on volume.restrict(s). This recovers the original actual_absolute_exchange at s=univ and preserves its absolute mathematical consequence in exposition. These consequences are preserved here without unused named wrappers."))),
                DescribeRole.Theorem))));
}
