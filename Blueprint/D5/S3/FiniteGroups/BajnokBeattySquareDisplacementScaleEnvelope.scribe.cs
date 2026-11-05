/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementScaleEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementScaleEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The positive finite fourth-order error shrinks like q^-6 and the unbounded negative correction remains exponentially damped. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementScaleEnvelopeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "In the Bajnok-Beatty lattice setting, the actual quotient return ratio has a fourth-order remainder bounded by an algebraic q^-6 term plus an explicit exponentially damped polynomial, all multiplied by p^-6.",
        H("The scale of the finite square-displacement remainder"),
        Blocks(
            Paragraph(Text(
                "Let p and q be signed integers satisfying p>=5, q>=3, Odd p and Odd q, and let t be any natural number with ((q+1)/2).toNat<=t. All odd composites are included. Put m=2*q*(t as Integer)-1 and n=(p*m).toNat. In the integer plane Fin 2 -> Integer, set v1a=![p*(m-1)/2,p*(m+1)/2], v2a=![p*(m-q^2)/2,-(p*(m+q^2)/2)], v1q=![p*(m-q)/2,p*(m+q)/2], and v2q=![p*(m-q)/2,-(p*(m+q)/2)]. The divisions by 2 are integer divisions exact by parity. The lattices Ka=Submodule.span Integer (Set.range ![v1a,v2a]) and Kq=Submodule.span Integer (Set.range ![v1q,v2q]) are their complete integer spans. For quotient maps Fa=Ka.mkQ.toAddMonoidHom and Fq=Kq.mkQ.toAddMonoidHom, write (Wa,Wq)=square_return_pair p q t=(W Fa n,W Fq n). These are complete quotient return counts.")),
            Describe.Lean(
                DescribeId.Create("actual-square-displacement-scale-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/BajnokBeattySquareDisplacementScaleEnvelope.actual_square_displacement_scale_envelope"),
                H("A fourth-order bound retaining the displacement scale"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write P=(p as Real), Q=(q as Real), nReal=P*(2*Q*(t as Real)-1), s=(Q^2-1)*P^2/(2*(nReal+1)), nu=Q^2, and N=nu-1. Define C=2*(nu+1)/(3*N^2), E=4/(3*N^2), Bcoef=16*(nu^2+nu+1)/(15*N^4), G=exp(s)+exp(-nu*s), H=C*s^3*(exp(s)-nu^2*exp(-nu*s)), and K=-E*s^3*(exp(s)-nu*exp(-nu*s))+Bcoef*s^5*(exp(s)-nu^3*exp(-nu*s))+(C^2/2)*s^6*(exp(s)+nu^4*exp(-nu*s)).")),
                    Paragraph(Text(
                        "For every p,q,t in the full signed domain above, 2/3<=s<=5/7 implies |2*(Wa as Real)/(Wq as Real)-G-H/P^2-K/P^4|<=[17/N^3+(8*nu+27*nu^2/100+4*nu^3/375)*exp(-2*nu/3)]/P^6. There is no assumed count identity, logarithmic expansion, envelope, remainder estimate or sign in the theorem's hypotheses. The earlier bound 2439/(8000*P^6) also remains available.")),
                    Paragraph(Text(
                        "ThresholdBracket.state_data supplies natural n,a,r with (n as Integer)=p*(2*q*t-1), n+p.toNat=2*a, 2*r=(q.toNat-1)*p.toNat, a+(q.toNat+1)*r<=n, Wa=2*(choose(n,a)+choose(n,a+(q.toNat+1)*r)), and Wq=4*choose(n,a+r). The fit inequality proves choose(n,a+r)>0. With A=choose(n,a), B=choose(n,a+r), and D=choose(n,a+(q.toNat+1)*r), the actual ratio is exactly (A+D)/B. This uses the same classification of the complete quotient counts as the earlier envelopes.")),
                    Paragraph(Text(
                        "Put R=nReal+1 and eps=P^(-2). The shared finite_log_data proof uses the centered finite products A/B=product(i<r)((1+x_i)/(1-x_i)) and B/D=product(i<q.toNat*r)((1+y_i)/(1-y_i)), where x_i=(P+2*i+1)/R and y_i=(Q*P+2*i+1)/R. Let L=log(A/B), M=log(B/D), a=C*s^3, b=Bcoef*s^5-E*s^3, ay=nu^2*C*s^3, and by=nu^3*Bcoef*s^5-nu*E*s^3. The exact first, third and fifth AP moments and the finite log bounds give L=s+a*eps+b*eps^2+rx and M=nu*s+ay*eps+by*eps^2+ry, together with L-s>=0 and M-nu*s>=0. The old residual bounds |rx|<=eps^3/50 and |ry|<=8*nu*eps^3 are retained.")),
                    Paragraph(Text(
                        "The positive numerator satisfies P+2*i+1<=Q*P. Using R=N*P^2/(2*s) and s<=5/7 therefore gives x_i<=kx/P with kx=10*Q/(7*N). Since Q>=3, N>=8 and nu/N<=9/8. Consequently kx^2<=225/(98*N)<=225/784=(15/28)^2 and 1/(1-kx^2/25)<=784/775. This keeps the displacement dependence that is lost by replacing kx with the uniform constant 15/28.")),
                    Paragraph(Text(
                        "For 0<=z<=kx/P, the same finite fifth-order logarithmic truncation bounds its nonnegative tail by [3*kx^4/(1-kx^2/25)]*eps^2*((2/3)*z^3). Summing and using the exact cubic moment gives 0<=Tx<=[3*kx^4/(1-kx^2/25)]*a*eps^3. The exact fifth AP identity also gives rx=-U*s^5*eps^3+V*s^5*eps^4+Tx, with U=16*(nu+1)/(3*N^4) and V=112/(15*N^4). This is the shared finite product and moment proof used by both envelopes.")),
                    Paragraph(Text(
                        "The rational coefficient inequalities C<=5/(6*N), Bcoef<=91/(60*N^2), U<=20/(3*N^3), and V<=14/(15*N^3), together with E=4/(3*N^2), imply 0<=a<=625/(2058*N)<=1/(3*N). Both Bcoef*s^5 and E*s^3 lie between zero and 1/(2*N^2), so |b|<=1/(2*N^2). The tail coefficient and the two explicit fifth-moment residuals then give |rx|<=(3180700/521017)*eps^3/N^3<7*eps^3/N^3.")),
                    Paragraph(Text(
                        "Normalize the positive correction by w=eps/N<=1/200. Writing aa=a*N and bb=b*N^2 gives 0<=aa<=1/3, |bb|<=1/2, and dx=L-s=aa*w+bb*w^2+rx>=0. Direct estimates give dx<=7*w/20<=1, |dx-aa*w|<=3*w^2/5, and |dx^2-(aa*w)^2|<=21*w^3/50. The existing positive cubic exponential estimate is at most dx^3<=343*w^3/8000. Hence |exp(dx)-1-aa*w-(bb+aa^2/2)*w^2|<=(7+21/100+343/8000)*w^3. Multiplying by exp(s)<=9/4 gives the coefficient 522207/32000<17.")),
                    Paragraph(Text(
                        "For the negative correction dy=M-nu*s, the existing nonlinear_blocks estimate is reused with its full unbounded domain: |exp(-dy)-1+ay*eps-(-by+ay^2/2)*eps^2|<=(8*nu+27*nu^2/100+4*nu^3/375)*eps^3. Its analytic input is the global inequality |exp(-u)-1+u-u^2/2|<=u^3/6 for every u>=0. No condition dy<=1 is imposed. The pointwise constant for this block remains 45/28. Multiplication by exp(-nu*s)<=exp(-2*nu/3) preserves an explicit exponential factor instead of taking a uniform maximum.")),
                    Paragraph(Text(
                        "Finally A/B=exp(s)*exp(dx) and D/B=exp(-nu*s)*exp(-dy). Their quadratic polynomials in eps combine exactly into G+H/P^2+K/P^4. The positive remainder is of order P^-6*N^-3, which agrees with the natural (p*q)^-6 scale as q grows; the other remainder is a polynomial in nu times exp(-2*nu/3). A q-independent positive error constant cannot express this vanishing remainder when p is fixed and q grows. A fixed-p threshold limit and a signed sixth-order asymptotic require separate formalization and are not asserted here.")),
                    Paragraph(Text(
                        "The Bajnok-Beatty setting and the quotient-count classification, centered finite products, AP moment identities, logarithmic truncations, and global negative cubic estimate are attributed to the repository priors. This statement is finite and uniform over the given odd domain. It makes no literature novelty, interpolation, equality-at-threshold, or signed residual claim."))),
                DescribeRole.Theorem)
        )));
}
