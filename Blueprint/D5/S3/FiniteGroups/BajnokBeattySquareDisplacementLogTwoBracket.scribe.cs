/* GID: D5/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket
   generality: I
   mirror-B: D5/B/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The complete all-odd actual-count threshold satisfies both log-two bounds. */

using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementLogTwoBracketDocument
    : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An all-q log-two bracket for the unique threshold of actual square-displacement return counts.",
        H("The log-two threshold bracket"),
        Blocks(Describe.Lean(
            DescribeId.Create("square-displacement-log-two-bracket"),
            DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattySquareDisplacementLogTwoBracket.actual_square_displacement_log_two_bracket"),
            H("The complete actual-count threshold and both bounds"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let p and q be signed integers with p>=5, q>=3, Odd p and Odd q. All odd composites are included. Write L=log(2), r=p/(4L), tmin=((q+1)/2).toNat, tlate=((qp+1)/2).toNat and tG=(q^2-1)p/(4qL)+1/(2q)-1/(2qp). There exists exactly one natural T satisfying all seven clauses: tmin<T; Wq(t)<Wa(t) for every natural t with tmin<=t<T; Wa(T)<=Wq(T); Wa(t)<Wq(t) for every natural t>T; T<=tlate; tG<T as real numbers; and T<=ceil(pq/(4L)) as integers. No equality at the crossing is asserted.")),
                Paragraph(Text("The two counts are exactly the components of square_return_pair p q t. Put m=2qt-1 and n=(pm).toNat. In the integer plane use v1a=(p(m-1)/2,p(m+1)/2), v2a=(p(m-q^2)/2,-p(m+q^2)/2), v1q=(p(m-q)/2,p(m+q)/2), v2q=(p(m-q)/2,-p(m+q)/2), with integer division. Let Ka and Kq be the complete integer spans of the respective pairs and Fa,Fq the quotient homomorphisms. Wa(t)=W(Fa,n) and Wq(t)=W(Fq,n), where W counts every signed coordinate word of length n returning to zero. These definitions use the complete quotients and the four signed coordinate steps.")),
                Paragraph(Text("For admissible states the existing state-data theorem identifies Wa=2(A+D) and Wq=4B with A=choose(n,a), B=choose(n,a+h), D=choose(n,a+(q+1)h), n+p=2a and 2h=(q-1)p. The exact centered coordinate is v=t-1/(2q)+1/(2qp)>0. With kappa=(q^2-1)/(4q), nu=q^2, N=nu-1 and s=kappa*p/v, it agrees with s=Np^2/(2(n+1)). The original finite signs give Wq<Wa for s>5/7 and Wa<Wq for 2/5<=s<=2/3. Every admissible t<=tlate has s>2/5.")),
                Paragraph(Text("On the whole band 2/3<=s<=5/7 the shared finite-log data give exp(Lx)=A/B, exp(-Ly)=D/B, Lx>=s, and exp(-Ly)>0. Hence the actual ratio R=2Wa/Wq is strictly greater than exp(s). For the upper bound use the existing q-scaled fourth-order envelope R=exp(s)+exp(-nu*s)+H/p^2+K/p^4+error, with absolute error at most [17/N^3+(8nu+27nu^2/100+4nu^3/375)exp(-2nu/3)]/p^6. Here C=2(nu+1)/(3N^2), E=4/(3N^2), B4=16(nu^2+nu+1)/(15N^4), H=C*s^3*(exp(s)-nu^2*exp(-nu*s)), and K=-E*s^3*(exp(s)-nu*exp(-nu*s))+B4*s^5*(exp(s)-nu^3*exp(-nu*s))+(C^2/2)*s^6*(exp(s)+nu^4*exp(-nu*s)).")),
                Paragraph(Text("The shared moments imply nu^j*exp(-nu*s)<=9^j/400 for j=1,2,3,4. Together with exp(s)<=9/4, C<=5/(6N) and B4<=91/(60N^2), they give 0<=H<=1875/(2744N) and abs(K)<=46876315/(15059072N^2). Also N*exp(-nu*s)<=9/400 and N*(8nu+27nu^2/100+4nu^3/375)*exp(-2nu/3)<=457407/200000. Since p>=5 and N>=8, R-exp(s) is at most [9/400+(1875/2744)/25+(46876315/15059072)/(8*625)+(17/64+457407/200000)/15625]/N. The numerator is exactly 297759604377663/5882450000000000<1/10. Thus 0<R-exp(s)<=1/(10N) throughout the band.")),
                Paragraph(Text("The logarithm bounds 2/3<L<7/10 follow from the library's rigorous rational bounds for log(2). If the original unique threshold satisfied T<=tG, its centered coordinate would be at most kappa*p/L, so s(T)>=L. Above 5/7 the exact high sign contradicts Wa(T)<=Wq(T). Within the band, R(T)>exp(s(T))>=exp(L)=2 gives the same contradiction. Therefore tG<T strictly.")),
                Paragraph(Text("For the upper bound let x=rq and u=ceil(x), viewed as a natural number. One has x>tmin and therefore u>=tmin. If u>=tlate, the original threshold bound suffices. Otherwise s(u)>2/5. Set a0=2L(p-1)/p^2. The polynomial certificate (p-5)(4p-5)>=0 and L<7/10 give 0<a0<=28/125. Direct scalar algebra at x gives s0=L*N/(nu-a0), with s0<L and L-s0=L*(1-a0)/(nu-a0)>=194/(375nu). Since N/nu>=8/9, N*(L-s0)>=1552/3375>1/10. As u>=x, the actual coordinate satisfies s(u)<=s0.")),
                Paragraph(Text("If s(u)>=2/3, apply exp(L)-exp(s)>=L-s for s>=0 and s<=L. This follows by multiplying exp(L-s)>=1+L-s by exp(s)>=1. The preceding margin gives exp(s(u))+1/(10N)<2, and hence R(u)<2 by the actual band estimate. If s(u)<2/3, the existing finite positive-cone sign applies because s(u)>2/5. In both cases Wa(u)<Wq(u). The original before-threshold law then forbids u<T, proving T<=ceil(pq/(4L)). Only scalar coordinates are evaluated at the real x; counts are evaluated at integer states.")),
                Paragraph(Text("Fix a signed odd integer p>=5 and set q_k=2k+3 for natural k. Let T(k) be the unique actual threshold satisfying the original five single-crossing clauses for p and q_k. Put r=p/(4log(2)) and delta=r-1/2+1/(2p). Dividing the strict lower bracket by q_k>0 and simplifying gives r-delta/q_k^2<T(k)/q_k. Since ceil(r*q_k)<r*q_k+1, the upper bracket gives T(k)/q_k<=r+1/q_k. Both bounding sequences tend to r as k tends to infinity, so the squeeze theorem yields T(k)/q_k -> p/(4log(2)). The full original single-crossing predicate and uniqueness hold for every k. Here p stays fixed; no estimate uniform in p, irrationality result or distribution theorem is asserted.")),
                Paragraph(Text("These are the actual marked quotient groups of the square-displacement growth family. On the admissible range, with Dgroup=(m^2-q^2)/2, the underlying groups are isomorphic to ZMod(p.natAbs) times ZMod((p*Dgroup).natAbs), with different coordinate markings. The parameter q varies the groups. The theorem concerns their exact signed-word return thresholds. The original single-crossing theorem supplies all five original clauses and uniqueness; the shared finite-log data, q-scaled fourth-order envelope and exact outside-band signs supply the two additional bounds. The lattice setting follows the Bajnok-Beatty source and the named repository developments; no literature-novelty claim is made."))),
            DescribeRole.Theorem))));
}
