using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class PositiveHankelL2Document : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual positive-half-line L2 Hankel domains, complete Laplace-square series, and the quarter-rate pi Schur bound.",
        H("Literal positive Hankel integrals on arbitrary complex L2 sources"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-half-rate-hankel-domain-series"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/PositiveHankelL2.positive_hankel_actual_l2_domain"),
            H("Actual Hankel domains and the full Laplace-square series for k>=1/2"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The literal kernel is K_k(s+t)=exp(-k*(s+t))/(1-exp(-(s+t))) on s,t>0. At k>=1/2 the Carleman majorant supplies both the absolute double-integral domain and the pi bound. The actual complex Hankel integral equals the complete sum over n>=0 of normSq of the literal Laplace integral at k+n.")),
                Paragraph(Text("Every Laplace integral is paid by the existing RightExponentialTail.right_exponential_tail_l2_integrable_and_sq_le at t=0. Actual absolute domination pays the infinite-sum interchange. All nine outputs are retained: absolute integrability and its bound, complex integrability, all Laplace domains, summability, the literal equality, positivity, zero imaginary part, and the form bound.")),
                Paragraph(Text("The theorem is a live supplier for the k+1 tail in the all-positive-rate proof. The Schur and Carleman method is classical; no novelty claim is attached to that method."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("actual-all-positive-hankel-domain-series"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/PositiveHankelL2.positive_hankel_actual_l2_domain_all_positive_rates"),
            H("The same actual domains and full series at every k>0"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The exact split K_k(x)=exp(-k*x)+K_(k+1)(x) pays the first term by the actual exponential-tail L2 estimate and reuses the half-rate result on the remaining tail. This retains all positive rates, including 0<k<1/4, with the bound (pi+1/(2*k)) times the input L2 mass.")),
                Paragraph(Text("The complete original Laplace-square sum is recovered by a legitimate shift of its summable tail, not by assuming that the actual Hankel integral equals a series. The first rank-one term is a genuinely integrable product. This theorem supplies the already proved complex domain and series used in the quarter-rate refinement."))),
            DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("actual-quarter-hankel-pi-schur-domain"),
            DeclarationHandle.Create(
                "D5/S3/Weil/ZetaGamma/FormCore/PositiveHankelL2.positive_hankel_actual_l2_domain_quarter_sharp"),
            H("The quarter-rate Schur row extends the pi bound to k>=1/4"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Use the positive Schur weight h(s)=exp(-s/4)/sqrt(1-exp(-s)), s>0. The weight is singular at zero and is not used as an L2 vector. The substitution s=log(1+q^2) has positive Jacobian 2*q/(1+q^2) and transforms K_(1/4)(t+s)*h(s)*ds exactly to 2*exp(-t/4)/(q^2+1-exp(-t))*dq.")),
                Paragraph(Text("The existing actual Cauchy integral gives integral(K_(1/4)(t+s)*h(s),s>0)=pi*h(t). The injective Jacobian integrability equivalence proves the actual row L1 domain before the row is used. Normalizing by h(t), applying weighted AM-GM, and proving the real product majorant integrable gives the absolute Hankel bound pi times the original L2 mass.")),
                Paragraph(Text("Exponential monotonicity gives 0<=K_k<=K_(1/4) for k>=1/4. The final theorem preserves the same complete nine-clause domain and Laplace-series output and improves both bounds to pi. It reuses the all-positive-rate series rather than duplicating its proof.")),
                Paragraph(Text("Mathlib supplies integrable_inv_one_add_sq, integral_Ioi_inv_one_add_sq, and the injective real Jacobian integral and integrability formulas.")),
                Paragraph(Text("The result concerns this literal positive Hankel form. It proves an upper bound, not equality of the operator norm with pi, and it does not identify an original Gamma/Fourier energy or establish complete-energy positivity or RH."))),
            DescribeRole.Theorem))));
}

