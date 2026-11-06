/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: A uniform corrected-center bracket retains the complete actual-count threshold signs. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementThresholdBracketDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite uniform estimate locates the complete actual-count single crossing for every odd square displacement, with its explicit Perron correction.",
        H("The corrected threshold bracket for all odd square displacements"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("bajnok-beatty-square-displacement-threshold-bracket"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/BajnokBeattySquareDisplacementThresholdBracket.actual_square_displacement_threshold_bracket"),
                H("The unique original threshold lies between the corrected tests"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For all signed integers p and q with p>=5, q>=3, Odd p and Odd q, including composite p and q, set nu=(q as a real)^2, beta=dbonacciPerronRoot(q.toNat^2), sigma=log(beta), alpha=(nu-1)/(4q sigma), d=((nu+1)sigma/(6q(nu-1)))*(((nu^2+1)beta-2nu^2)/((nu+1)beta-2nu)), b=d-1/(2q), c=alpha*p+1/(2q)+b/p, and epsilon=q/(10p^3). Products, quotients and powers in these coefficient formulas are real operations. Let tmin=((q+1)/2).toNat and tlate=((q*p+1)/2).toNat, with integer division before toNat. There exists exactly one natural T satisfying ALL of the following conditions together: tmin<T; for every natural t with tmin<=t<T, Wq(t)<Wa(t); Wa(T)<=Wq(T); for every natural t>T, Wa(t)<Wq(t); T<=tlate; c-epsilon<(T as a real); and (T as an integer)<=Int.ceil(c+epsilon). The before and after quantifiers cover the entire original natural domain.")),
                    Paragraph(Text(
                        "The counts are the repository's actual square_return_pair p q t, never supplied sign or count hypotheses. Explicitly m=2qt-1, n=(p*m).toNat, v1a=(p(m-1)/2,p(m+1)/2), v2a=(p(m-q^2)/2,-p(m+q^2)/2), v1q=(p(m-q)/2,p(m+q)/2), and v2q=(p(m-q)/2,-p(m+q)/2), with integer vector coordinates and integer division. Ka and Kq are the complete integer spans of their respective two generators. Fa and Fq are the canonical quotient homomorphisms from the integer plane, and Wa=W Fa n and Wq=W Fq n count all signed coordinate words returning to zero. This is the broad Bajnok-Beatty setting of different lattice markings in the common finite quotient-group family; the present result adds a uniform count threshold estimate and does not introduce a new group-classification theorem.")),
                    Paragraph(Text(
                        "At a valid integer state define P=p.toNat, Q=q.toNat, a=(q*p*t).toNat, and r=(((q-1)*p)/2).toNat. The completed SingleCrossing actual_counts supplier gives Wa=2(A+D), Wq=4B, with A=Nat.choose n a, B=Nat.choose n (a+r), and D=Nat.choose n (a+(Q+1)r). All three binomials are positive: n+P=2a and a+(Q+1)r<=n. Thus 2Wa/Wq=(A+D)/B. Set kappa=(nu-1)/(4q), v=t-1/(2q)+1/(2qp), and s=kappa*p/v=(nu-1)p^2/(2(n+1)). The completed Envelope theorem applies only at integer states with 2/3<=s<=5/7. It bounds the absolute difference between 2Wa/Wq and Qp(s)=G(s)+H(s)/p^2 by 1/(5p^4), where G(s)=exp(s)+exp(-nu*s), C=2(nu+1)/(3(nu-1)^2), and H(s)=C*s^3*(exp(s)-nu^2 exp(-nu*s)). No real-variable binomial function is defined.")),
                    Paragraph(Text(
                        "PerronRoot monotonicity and the small order-nine exponential certificate give 200/291<sigma<7/10, while the Perron reciprocal identity gives G(sigma)=2. Correction supplies 0<d<5log(2)/(24q)<7/(48q), -1/(2q)<b<0, and the exact cancellation g*k=H(sigma), with g=exp(sigma)-nu exp(-nu*sigma) and k=sigma*d/alpha. The existing Profile theorem gives Gaussian secant slope at least 161/90 for s>=2/3. Its rational tail bound gives nu^2 exp(-nu*s)<9/10 and nu^3 exp(-nu*s)<=81/10. Since C<=5/48 and exp(s)<=9/4 on the band, H has nonnegative derivative bounded by 4125/5488<1. Hence H has secants between zero and the interval length, and Qp retains secant slope at least 161/90.")),
                    Paragraph(Text(
                        "At vc=alpha*p+d/p and sc=kappa*p/vc put delta=sigma-sc and rcenter=k/p^2-delta. The coefficient estimates give d/alpha<=1/16, k<=1/25, nu*k<=1/3, 0<=delta<=k/p^2 and 0<=rcenter<=1/(400p^4). The existing two quadratic exponential remainders, with the positive displacement nu*delta<=1, give 0<=G(sc)-2+g*delta<=2delta^2. Exact cancellation and the H secant bound then yield a center residual at most (2/400+2/625+1/25)/p^4=241/(5000p^4)<1/(20p^4). This finite inference explains the correction instead of treating it as an assumed coefficient.")),
                    Paragraph(Text(
                        "Both vc-epsilon and vc+epsilon lie between 7kappa*p/5 and 3kappa*p/2, so their s-coordinates lie in the envelope band. Their distance epsilon from vc changes s by at least 64/(405p^4), using kappa>=2q/9 and v<=3qp/8. The secant gain exceeds the center and envelope errors because (161/90)*(64/405)-1/20-1/5=2383/72900>0. Therefore Qp(s(vc-epsilon))>2+1/(5p^4) and Qp(s(vc+epsilon))<2-1/(5p^4). These are estimates of exponentials and rational coordinates; actual counts enter only at integer states.")),
                    Paragraph(Text(
                        "The lower bracket uses the exact threshold from SingleCrossing. Since v(t)=vc+t-c, a hypothetical T<=c-epsilon forces s(T)>=s(vc-epsilon). In the band the envelope contradicts Wa(T)<=Wq(T). Above 5/7 the exact finite centered product gives log(A/B)>=s(T)>5/7>log(2), so A>2B, again contradicting the comparison at T. For the upper bracket let U=ceil(c+epsilon). The rational bounds show U>=tmin. If U>=tlate then T<=U follows directly. Otherwise U is a valid integer state with 2/5<s(U)<=s(vc+epsilon)<=5/7. The band branch gives Wa(U)<Wq(U) from the envelope; the original strict before condition then forces T<=U.")),
                    Paragraph(Text(
                        "The remaining upper branch uses a genuine finite positive cone on 2/5<=s<=2/3. Write x_i=(p+2i+1)/(n+1) for i<r. The correct uniform estimate is x_i<=1/(2p)<=1/10. The proposed stronger 1/(3p) estimate is not used. The exact cubic moment Ux=(2/3)sum x_i^3 equals C*s^3/p^2-[4/(3(nu-1)^2)]*s^3/p^4 and is at most 1/810. The pinned n=2 logarithmic truncation gives log((1+x)/(1-x))<=2x+(2/3)x^3+2x^5/(1-x^2); x^2<=1/100 bounds its tail by (1/33)*((2/3)x^3). Thus log(A/B)<=2/3+(34/33)/810=8927/13365<67/100, with surplus 551/267300. The finite n=4 exponential bound gives exp(67/100)<=1251246427/640000000<49/25. The other exact product gives log(B/D)>=nu*s>=18/5, while sum over i<6 of (18/5)^i/i! is 482707/15625>30. Hence D/B<1/30 and (A+D)/B<49/25+1/30=2-1/150<2. For every valid t<=tlate, the strict lower bound s>2/5 follows from n<=nu*p^2+(q-1)p and (nu-5)p^2-4(q-1)p-4>=2(q-1)p(p-2)-4>=56. This closes the integer rounding step outside the envelope band.")),
                    Paragraph(Text(
                        "The lattice classifications, exact count formulas, SingleCrossing, Envelope, Correction, Profile, finite moment identities and quadratic remainder estimates are reused from the Bajnok-Beatty development. The new finite inference is the uniform corrected-center estimate and the integer positive-cone completion across all odd q. The conclusion retains the full threshold signs and both explicit rounding bounds. It does not assert count equality at T, real binomial interpolation, an exact formula T=ceil(c), or a general-q fourth-order expansion."))),
                DescribeRole.Theorem))));
}
