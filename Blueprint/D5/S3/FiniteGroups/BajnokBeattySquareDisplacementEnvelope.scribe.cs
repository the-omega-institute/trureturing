/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: Uniform finite-count control links square displacement to its Gaussian coefficient and profile. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementEnvelopeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact finite-binomial calculation controls the actual first-wrap lattice return ratio uniformly over every odd square displacement, with an explicit second-order term and error at most 1/(5p^4).",
        H("A uniform square-displacement envelope for actual counts"),
        Blocks(
            Paragraph(Text(
                "Let p,q,t be signed integers with p>=5, p odd, q>=3, q odd, and q+1<=2t. In particular neither p nor q is required to be prime, and q has no upper bound. Set m=2qt-1 and n=(pm).toNat. The ambient integer plane is Plane=Fin 2 -> Z. The actual generators are v1a=![p*(m-1)/2,p*(m+1)/2], v2a=![p*(m-q^2)/2,-(p*(m+q^2)/2)], v1q=![p*(m-q)/2,p*(m+q)/2], and v2q=![p*(m-q)/2,-(p*(m+q)/2)]. Every division by 2 in these vectors is integer division; parity makes these exact halves.")),
            Paragraph(Text(
                "Define Ka=Submodule.span Z (Set.range ![v1a,v2a]) and Kq=Submodule.span Z (Set.range ![v1q,v2q]). These are the complete integer spans. Let Fa:Plane ->+ (Plane/Ka) and Fq:Plane ->+ (Plane/Kq) be their quotient maps, specifically Ka.mkQ.toAddMonoidHom and Kq.mkQ.toAddMonoidHom. Let Wa=W Fa n and Wq=W Fq n be the original natural return-word counts. All four vectors, both spans, quotient maps, and counts are part of the theorem's original objects.")),
            Describe.Lean(
                DescribeId.Create("actual-square-displacement-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/BajnokBeattySquareDisplacementEnvelope.actual_square_displacement_envelope"),
                H("Exact second-order envelope on the full signed domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Put s=((q as Real)^2-1)*(p as Real)^2/(2*((n as Real)+1)), nu=(q as Real)^2, C=2*(nu+1)/(3*(nu-1)^2), G=exp(s)+exp(-nu*s), and H=C*s^3*(exp(s)-nu^2*exp(-nu*s)). Under the exact real hypotheses 2/3<=s and s<=5/7, the conclusion is |2*(Wa as Real)/(Wq as Real)-G-H/(p as Real)^2|<=1/(5*(p as Real)^4). The natural counts are cast to Real only at this ratio; their counting arguments remain natural numbers.")),
                    Paragraph(Text(
                        "The condition q+1<=2t implies m>q^2. The existing asymmetric_rank_one_actual_data supplies the sumDiff identities for the actual vectors. The complete closed-boundary classification odd_boundary_count_of_sumDiff then gives Wa=2*(A+D) and Wq=4*B, where a=(qpt).toNat, r=(((q-1)p)/2).toNat, A=choose(n,a), B=choose(n,a+r), and D=choose(n,a+(q+1)r). Here (q+1)r=((q^2-1)p)/2 as an exact integer identity. All indices lie between 0 and n. In particular B>0 by Nat.choose_pos, so Wq>0 before the count ratio is simplified. No count classification is assumed as a premise of the envelope.")),
                    Paragraph(Text(
                        "Write P=(p as Real), Q=(q as Real), R=(n as Real)+1. The natural relations n+p=2a and 2r=(q-1)p give 2(a+r)-n=qp. Applying choose_ratio_centered_prod at a with length r and at a+r with length qr gives A/B=product(i<r)((1+x_i)/(1-x_i)) and B/D=product(i<qr)((1+y_i)/(1-y_i)), where x_i=(P+2i+1)/R and y_i=(QP+2i+1)/R. Equivalently D/B is the product of (1-y_i)/(1+y_i). These are identities of finite products of positive factors, not interpolations of binomial coefficients.")),
                    Paragraph(Text(
                        "The existing arithmetic-progression suppliers sum_linear in BajnokBeattyOddWrapPositiveCone and sum_cubic in BajnokBeattyOddWrapGaussianEnvelope give the exact identities 2*sum(x_i)=s and 2*sum(y_i)=nu*s. With E=4/(3*(nu-1)^2), their cubic consequences are (2/3)*sum(x_i^3)=C*s^3/P^2-E*s^3/P^4 and (2/3)*sum(y_i^3)=nu^2*C*s^3/P^2-nu*E*s^3/P^4. These retain the finite negative corrections. For nu>=9 one has 0<C<=5/48, 0<E<=1/48, nu^2*C<=(15/16)*nu, and nu*E<=(5/2)*nu^2*C. The first and third upper bounds reduce to the nonnegative factors (nu-9)*(5nu+3) and (nu-9)*(13nu-5).")),
                    Paragraph(Text(
                        "There is no restriction of q to a finite range. The inequalities Q/(Q^2-1)<=3/8 and Q^2/(Q^2-1)<=9/8, together with s<=5/7, give 0<=x_i<=15/(28P) and 0<=y_i<=45/(28P); both are less than 1 when P>=5. The n=2 lower logarithmic truncation and n=3 upper truncation yield 0<=log((1+z)/(1-z))-2z-(2/3)z^3<=(2/5)z^5+2z^7/(1-z^2). For z<=k/P, its sum is at most B(k)/P^2 times the cubic sum (2/3)*sum(z^3), where B(k)=(3/5)*k^2+3*k^4/(25*(1-k^2/25)). Thus Bx=B(15/28)=1107/6076 and By=B(45/28)=336555/137788<5/2. Keeping these parameter-dependent tails is essential to the stated constant.")),
                    Paragraph(Text(
                        "Let Lx=log(A/B), Ly=log(B/D), eps=P^(-2), a0=C*s^3, A0=nu^2*C*s^3, dx=Lx-s, and dy=Ly-nu*s. The n=1 lower log bound gives dx,dy>=0. The positive residual has the exact form dx-a0*eps=-E*s^3*eps^2+Tx, with 0<=Tx<=Bx*a0*eps^2<=s^3*eps^2/48 and 0<=E*s^3<=s^3/48. Its absolute value is therefore at most s^3*eps^2/48, using the maximum of the two nonnegative parts. Also dx<=eps/25<=1. The existing positive quadratic exponential remainder and exp(s)<9/4 bound the weighted positive error by (271419/13720000)*eps^2.")),
                    Paragraph(Text(
                        "The negative residual is dy-A0*eps=-nu*E*s^3*eps^2+Ty, with 0<=Ty<=By*A0*eps^2<=(5/2)*A0*eps^2. Its absolute value is at most (5/2)*A0*eps^2, and dy<=(33/32)*nu*s^3*eps. The displacement dy itself has no uniform upper bound as q grows. The existing exp_negative_quadratic_remainder applies to EVERY dy>=0: |exp(-dy)-1+dy|<=dy^2/2. It has no dy<=1 hypothesis. Meanwhile real_rational_tail_on_ray gives nu^2*exp(-nu*s)<9/10 and consequently nu*exp(-nu*s)<1/10. Damping controls the entire negative error by [(15/64)*s^3+(9801/20480)*s^6]*eps^2, at most (71788125/481890304)*eps^2. This is why the estimate remains uniform for unbounded q, even when dy is very large.")),
                    Paragraph(Text(
                        "Finite exponentiation gives A/B=exp(s)*exp(dx) and D/B=exp(-nu*s)*exp(-dy). Adding their first-order displacements reconstructs H/P^2 exactly. The two rational error constants sum to 50825768013/301181440000<1/5, proving the stated finite inequality. No asymptotic remainder or real binomial interpolation is substituted for the integer counts.")),
                    Paragraph(Text(
                        "The existing square-displacement correction and profile describe the same Gaussian family G_q(s)=exp(s)+exp(-q^2*s) and its Perron parameter sigma_q=log(dbonacciPerronRoot(q^2)). At that parameter, exp(sigma_q)-nu^2*exp(-nu*sigma_q)>0 and the profile derivative is positive. The present finite-count theorem supplies an explicit second-order correction and uniform fourth-order error for the actual quotient counts on the s-band. It supplies a finite-count bridge to those coefficient and profile calculations. It does not assert a general-q single crossing, an integer threshold or rounding law, or literature novelty."))),
                DescribeRole.Theorem)
        )));
}
