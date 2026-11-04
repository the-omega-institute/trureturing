/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthEnvelope
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthEnvelope
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A generic fifth moment and globally damped negative cubic control the full finite count ratio. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementFourthEnvelopeDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quotient return counts in the Bajnok-Beatty lattice setting have a fourth-order correction with a uniform finite remainder 2439/(8000p^6), even though the negative logarithmic displacement is unbounded in q.",
        H("A fourth-order envelope for actual square-displacement counts"),
        Blocks(
            Paragraph(Text(
                "Let p and q be signed integers with p>=5, q>=3, Odd p and Odd q. Neither integer is required to be prime: all odd composites are included, and there is no upper bound on q. The time t is a natural number satisfying ((q+1)/2).toNat<=t. Put m=2*q*(t as Integer)-1 and n=(p*m).toNat. The ambient plane is Fin 2 -> Integer.")),
            Paragraph(Text(
                "The actual generators are v1a=![p*(m-1)/2,p*(m+1)/2], v2a=![p*(m-q^2)/2,-(p*(m+q^2)/2)], v1q=![p*(m-q)/2,p*(m+q)/2], and v2q=![p*(m-q)/2,-(p*(m+q)/2)]. All four divisions by 2 are integer divisions made exact by parity. Let Ka=Submodule.span Integer (Set.range ![v1a,v2a]) and Kq=Submodule.span Integer (Set.range ![v1q,v2q]); these are the complete integer spans, with no selection of a smaller sublattice. Their quotient maps are Fa=Ka.mkQ.toAddMonoidHom and Fq=Kq.mkQ.toAddMonoidHom. The pair square_return_pair p q t is exactly (W Fa n,W Fq n). Write this natural count pair as (Wa,Wq).")),
            Describe.Lean(
                DescribeId.Create("actual-square-displacement-fourth-envelope"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/BajnokBeattySquareDisplacementFourthEnvelope.actual_square_displacement_fourth_envelope"),
                H("Uniform finite fourth-order control on the full signed domain"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Set P=(p as Real), Q=(q as Real), nReal=P*(2*Q*(t as Real)-1), s=(Q^2-1)*P^2/(2*(nReal+1)), and nu=Q^2. Define C=2*(nu+1)/(3*(nu-1)^2), E=4/(3*(nu-1)^2), and Bcoef=16*(nu^2+nu+1)/(15*(nu-1)^4). The uncorrected profile is G(s)=exp(s)+exp(-nu*s). Its second-order coefficient is H(s)=C*s^3*(exp(s)-nu^2*exp(-nu*s)). The fourth-order coefficient is K(s)=-E*s^3*(exp(s)-nu*exp(-nu*s))+Bcoef*s^5*(exp(s)-nu^3*exp(-nu*s))+(C^2/2)*s^6*(exp(s)+nu^4*exp(-nu*s)).")),
                    Paragraph(Text(
                        "For every p,q,t in the stated domain, the additional band condition 2/3<=s<=5/7 implies |2*(Wa as Real)/(Wq as Real)-G(s)-H(s)/P^2-K(s)/P^4|<=2439/(8000*P^6). Since P>=5 and 2439/8000<1, this remainder is strictly smaller than 1/P^6. The theorem states the sharper bound alone. Its hypotheses contain no assumed count comparison, logarithmic expansion, remainder estimate, sign, or finite envelope.")),
                    Paragraph(Text(
                        "The exact lattice classification supplies natural n,a,r with (n as Integer)=p*(2*q*t-1), n+p.toNat=2*a, 2*r=(q.toNat-1)*p.toNat, and a+(q.toNat+1)*r<=n. It also supplies Wa=2*(choose(n,a)+choose(n,a+(q.toNat+1)*r)) and Wq=4*choose(n,a+r). Thus nReal=(n as Real). With A=choose(n,a), B=choose(n,a+r), and D=choose(n,a+(q.toNat+1)*r), the actual ratio 2Wa/Wq is exactly (A+D)/B. The fit inequality gives B>0 before division. This classification is reused from ThresholdBracket.state_data and SingleCrossing.square_return_pair, rather than assumed.")),
                    Paragraph(Text(
                        "Let R=nReal+1. The existing choose_ratio_centered_prod supplies the exact finite products A/B=product(i<r)((1+x_i)/(1-x_i)) and B/D=product(i<q.toNat*r)((1+y_i)/(1-y_i)), where x_i=(P+2*i+1)/R and y_i=(Q*P+2*i+1)/R. On the band one has 0<=x_i<=15/(28P) and 0<=y_i<=45/(28P), so every factor and every logarithm argument is positive. Put Lx=log(A/B), Ly=log(B/D), and eps=P^(-2).")),
                    Paragraph(Text(
                        "The existing AP sum_linear and sum_cubic identities supply the first and third moments. The additional generic fifth identity uses F5(x)=x^6-5*x^4+7*x^2: 12*sum(i<r)(a+2*i+1)^5=F5(a+2*r)-F5(a). It follows by finite induction from F5(x+2)-F5(x)=12*(x+1)^5. Applying this same identity to both blocks gives (2/5)*sum(x_i^5)=Bcoef*s^5*eps^2-U*s^5*eps^3+V*s^5*eps^4 and (2/5)*sum(y_i^5)=nu^3*Bcoef*s^5*eps^2-nu^2*U*s^5*eps^3+nu*V*s^5*eps^4, where U=16*(nu+1)/(3*(nu-1)^4) and V=112/(15*(nu-1)^4).")),
                    Paragraph(Text(
                        "The finite n=3 lower and upper log truncations retain 2z+(2/3)z^3+(2/5)z^5 and bound the remaining tail between zero and 2z^7/(1-z^2). For 0<=z<=k/P and P>=5, z^2<=k^2*eps and eps<=1/25. Consequently this tail is at most [3*k^4/(1-k^2/25)]*eps^2*((2/3)*z^3). Summing and using the exact cubic moments yields nonnegative Tx,Ty with Tx<=[3*(15/28)^4/(1-(15/28)^2/25)]*ax*eps^3 and Ty<=[3*(45/28)^4/(1-(45/28)^2/25)]*ay*eps^3.")),
                    Paragraph(Text(
                        "The full logarithmic expansions are Lx=s+ax*eps+bx*eps^2+rx and Ly=nu*s+ay*eps+by*eps^2+ry, with ax=C*s^3, bx=Bcoef*s^5-E*s^3, ay=nu^2*C*s^3, by=nu^3*Bcoef*s^5-nu*E*s^3, rx=-U*s^5*eps^3+V*s^5*eps^4+Tx, and ry=-nu^2*U*s^5*eps^3+nu*V*s^5*eps^4+Ty. The first-moment log lower bound separately proves dx=Lx-s>=0 and dy=Ly-nu*s>=0; no sign is assumed for bx or by.")),
                    Paragraph(Text(
                        "For nu>=9 the existing coefficient certificate gives C<=5/48, E<=1/48, and nu^2*C<=(15/16)*nu. The additional rational certificates give Bcoef<=91/3840, nu^2*Bcoef<=2457/1280, U<=5/384, nu*U<=15/128, and V<=7/3840. Clearing positive denominators reduces these to the factored positive polynomials (nu-9)*(91nu^3+455nu^2+545nu+445), (nu-9)*(3275z^3+84320z^2+725120z+2082816) with z=nu-9, (nu-9)*(5nu^3+25nu^2+255nu+227), and (nu-9)*(3nu+5)*(15nu^2+50nu-1), together with (nu-1)^4>=4096.")),
                    Paragraph(Text(
                        "These finite certificates imply 0<=ax<=1/20, |bx|<=1/50, |rx|<=eps^3/50, 0<=ay<=(7/20)*nu, |by|<=(2/5)*nu, and |ry|<=8*nu*eps^3. The residual numerical certificates are 1991705/133380352<1/50 and 71086166275/9074166528<8. In particular dx<=eps/10 and |dx-ax*eps|<=(13/625)*eps^2, whereas dy<=(2/5)*nu*eps and |dy-ay*eps|<=(18/25)*nu*eps^2.")),
                    Paragraph(Text(
                        "The decisive analytic step treats every u>=0: |exp(-u)-1+u-u^2/2|<=u^3/6. For P3(u)=1-u+u^2/2-u^3/6, the derivative of P3(u)*exp(u) is -(u^3/6)*exp(u)<=0 on the nonnegative ray. Antitonicity therefore gives P3(u)<=exp(-u). Combining this with the existing global negative quadratic upper bound exp(-u)<=1-u+u^2/2 proves the absolute cubic inequality. Only the positive block uses a bounded displacement: dx<=eps/10<=1 permits the pinned finite Real.exp_bound' with n=3 and quadratic_le_exp_of_nonneg.")),
                    Paragraph(Text(
                        "Assuming dy<=1 would be false on the stated domain: its leading correction ay*eps grows proportionally to nu*eps as q grows along band states with fixed p. The proof never uses that assumption. It obtains |exp(dx)-1-ax*eps-(bx+ax^2/2)*eps^2|<=(141/6250)*eps^3 and |exp(-dy)-1+ay*eps-(-by+ay^2/2)*eps^2|<=[8nu+(27/100)nu^2+(4/375)nu^3]*eps^3 from the global negative cubic bound and the exact finite logarithmic residuals.")),
                    Paragraph(Text(
                        "The existing FourthCoefficient.quartic_tail gives nu^4*exp(-2nu/3)<6561/400. For j=1,2,3, multiplying nu^j*exp(-nu*s) by nu^(4-j)>=9^(4-j), and using s>=2/3, gives nu^j*exp(-nu*s)<=9^j/400. This reuses one quartic certificate without repeating its exponential lower bound or derivative calculation. Together with exp(s)<=9/4, it bounds the weighted positive error by (1269/25000)*eps^3 and the weighted negative error by (50823/200000)*eps^3. Their sum is exactly (2439/8000)*eps^3.")),
                    Paragraph(Text(
                        "Finally A/B=exp(s)*exp(dx) and D/B=exp(-nu*s)*exp(-dy). Adding their degree-one and degree-two polynomials in eps reconstructs H(s)*eps and K(s)*eps^2 exactly. This is a finite statement about natural binomial coefficients and the complete quotient counts. The Bajnok-Beatty setting, lattice return classification, centered finite products, cubic moments, quadratic estimates, and Gaussian profile come from the repository priors. No literature novelty, refined threshold, interpolation, or equality claim is made."))),
                DescribeRole.Theorem)
        )));
}
