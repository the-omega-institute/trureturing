using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualDeficitFourBandDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual strict deficit-four band preserves adjacent depth and finite inherited first-child spines.",
        H("Actual Cloitre Deficit-Four Band"),
        Blocks(
            Paragraph(Text(
                "F is the Fibonacci sequence with F(0)=0 and F(1)=1. Put "
                + "phi=(1+sqrt(5))/2 and G(n)=floor((n+1)/phi). C is the actual "
                + "positive-index Cloitre sequence with C(1)=C(2)=1. Its legal domain is "
                + "D(N)=[1,N-1], its inner map is T(N,x)=N-C(x), and its orbit X(N,i) "
                + "starts at N-1. The prescribed depth is d(N)=C(N-1), the selected "
                + "point is g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N>=3. "
                + "Put Q(m,t)=F(m-1)-C(F(m)-t) on the full natural closed block "
                + "0<=t<=F(m-2). The upper cap makes Q the exact nonnegative integer "
                + "difference. It is distinct from the golden excess C(n)-G(n).")),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full30-4"),
                DeclarationHandle.Create("D5/S1/Recurrence/Invariants/CloitreActualDeficitFourBand.full30_4"),
                H("Strict band, adjacent rows and finite critical spines"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Hyp24_1(U) includes the complete inherited Hyp21_1: the finite "
                        + "ratio condition 22877*C(n)<=15225*n for "
                        + "16384<=n<=131071; the full golden base and equality classification "
                        + "for 1<=n<=65535; and prescribed periodic entry for 3<=N<=52. "
                        + "The golden base states G(n)<=C(n), with equality implying "
                        + "n=F(j) or F(j)+1 for some j>=2, n+1=F(j) for an odd j>=3, "
                        + "or n in {11,24,25,59}. "
                        + "For every positive n, the global bounds are 1<=C(n) and "
                        + "G(n)<=C(n)<=U(n)<=n. The upper function satisfies "
                        + "U(1)=1, the piecewise formula U(n)=min(n-F(j-2),F(j)) on "
                        + "F(j)<=n<F(j+1) for j>=3, and monotonicity and increments "
                        + "U(n)<=U(n+1)<=U(n)+1 on positive indices. For j>=2, "
                        + "U(F(j))=C(F(j))=G(F(j))=F(j-1); for j>=3, "
                        + "C(F(j)+1)=G(F(j)+1)=F(j-1)+1. For every q>=6 and t>=0, "
                        + "the right collar [F(q-1),F(q-1)+t] is legal and invariant "
                        + "under T(F(q)+t), captures every legal orbit, and contains every "
                        + "legal periodic point. For each N>=3, the earliest periodic "
                        + "entry of X(N,i) precedes or equals d(N). "
                        + "Hyp24_1 also includes C(F(j)-1)=F(j-1) for j>=5, "
                        + "and for j>=6 and 0<=b<=F(j-1), with N=F(j+1)-b, "
                        + "the collar [F(j)-b,F(j)] intersected with D(N) is invariant "
                        + "under T(N) and captures every legal orbit. Every legal periodic "
                        + "point x of T(N) satisfies max(F(j-1),F(j)-b)<=x and "
                        + "x<=min(F(j),F(j)+F(j-3)-b).")),
                    Paragraph(Text(
                        "Two additional finite full-block conditions are required. For every "
                        + "v<=F(18), Q(20,v)<=2 exactly when v<=35; when v>35, "
                        + "3<=Q(20,v)<=max(3,v-36). For every v<=F(19), "
                        + "Q(21,v)<=3 exactly when v<=45; when v>45, "
                        + "4<=Q(21,v)<=max(4,v-46). These conditions and the inherited "
                        + "foundations are premises; no instance of them is asserted.")),
                    Paragraph(Text(
                        "Write Z(m)=3*m+floor((m-1)/3)-24 and B(m)=4*m-34. "
                        + "For every m>=21, B(m)+2<F(m-2). Every legal integer gap "
                        + "Z(m)<b<=B(m) has Q(m,b)=4. Define epsilon(m,b)=1 exactly "
                        + "when b=Z(m)+1 and m mod 3!=1, and zero otherwise.")),
                    Paragraph(Text(
                        "For m>=22 and Z(m)<b<B(m), put N=F(m)-b, "
                        + "z=F(m-1)-g(N) and w=F(m-2)-(N-g(N)). The exact parent "
                        + "and adjacent deficits are Q(m,b)=Q(m,b+1)=4. "
                        + "C(N)=C(N-1)=d(N)=F(m-1)-4 and X(N,0)=N-1. "
                        + "The actual gaps are z=b-4+epsilon(m,b), w=4-epsilon(m,b), "
                        + "and g(N)=F(m-1)-b+4-epsilon(m,b)=F(m-1)-z. "
                        + "The complementary route is N-g(N)=F(m-2)-w; z+w=b, "
                        + "z<=F(m-3) and w<=F(m-4). The signed jump "
                        + "K(N)=(g(N):Z)-(T(N,g(N)):Z) is -epsilon(m,b), "
                        + "with both terms cast before subtraction. The minimal period "
                        + "under this same T(N) is 1+epsilon(m,b). The selected gap "
                        + "satisfies Z(m-1)<z<B(m-1).")),
                    Paragraph(Text(
                        "For each M>=22 and legal strict-band b0, the physical spine "
                        + "is N_s=g^s(F(M)-b0), with inherited m_s=M-s and "
                        + "b_s=F(m_s)-N_s. For every s<=M-21, including order 21, "
                        + "N_s=F(m_s)-b_s and Z(m_s)<b_s<B(m_s). Both b_s and "
                        + "b_s+1 are legal, both deficits equal four, and "
                        + "C(N_s)=C(N_s-1)=d(N_s)=F(m_s-1)-4. On every edge "
                        + "s<M-21, N_(s+1)=g(N_s), m_(s+1)=m_s-1, "
                        + "b_(s+1)=F(m_s-1)-g(N_s)=b_s-4+epsilon(m_s,b_s). "
                        + "The actual complementary gap is 4-epsilon(m_s,b_s), "
                        + "the actual physical selector has the same formula, and the "
                        + "signed jump and minimal period are -epsilon and 1+epsilon. "
                        + "There is no outgoing order-21 edge in this contract.")),
                    Paragraph(Text(
                        "If also b<=B(m)-2, the three parent gaps b,b+1,b+2 "
                        + "give d(N)=d(N-1)=C(N)=C(N-1)=F(m-1)-4. "
                        + "The actual adjacent selector is g(N-1)=F(m-1)-b+3, "
                        + "with g(N-1)<=g(N) and g(N)-g(N-1)=1-epsilon(m,b). "
                        + "The actual first child satisfies d(g(N))=C(g(N)-1)=F(m-2)-4. "
                        + "When epsilon=1, g(N)=g(N-1) is the same natural physical "
                        + "index under the two different parent maps. The two "
                        + "complementary gaps are respectively three and four, and "
                        + "the minimal periods under T(N) and T(N-1) are two and one.")),
                    Paragraph(Text(
                        "For arbitrary finite M>=22, b0=Z(M)+1 is a legal strict-band "
                        + "root. At every node s<=M-21 its actual gap is Z(M-s)+1. "
                        + "At every edge s<M-21, K(N_s)=-1 exactly when "
                        + "(M-s) mod 3!=1; otherwise K(N_s)=0. Every positive fee "
                        + "max(K(N_s),0) is zero. Choosing M arbitrarily large gives "
                        + "arbitrarily long finite critical spines; one finite root "
                        + "is not given an infinite descending spine.")),
                    Paragraph(Text(
                        "At the non-strict endpoint b=B(m), m>=22, the parent "
                        + "has deficit four and the actual gaps are z=B(m-1), w=4. "
                        + "Its physical selector is F(m-1)-B(m-1), its complementary "
                        + "child is F(m-2)-4, its minimal period is one and its signed "
                        + "jump is zero. Q(m,B(m)+1) is four or five, so d(N) is "
                        + "F(m-1)-4 or F(m-1)-5. This endpoint is excluded from "
                        + "the strict depth equalities and strict child-band assertion.")),
                    Paragraph(Text(
                        "The sublevel induction uses Q(k,v)<=3 exactly when v<=Z(k), "
                        + "together with Q(k,v)=3 on Z(k)-3<=v<=Z(k). The complete "
                        + "finite seeds supply the initial row. The existing "
                        + "unweighted cone bounds exterior periodic images; the "
                        + "existing maximal platform makes complementary gaps at "
                        + "most four flat. At the critical two-point cycle, exterior "
                        + "sides alternate from the prescribed origin N-1. Sampling "
                        + "at the actual depth F(k-1)-4 fixes the selected phase. "
                        + "The Fibonacci divisibility criterion supplies the width "
                        + "increment. Closed-band qualification then feeds the existing "
                        + "full deficit-four selector at first-hit times zero or one. "
                        + "Adjacent depths and the finite spines use these same actual "
                        + "producer rows and inherited natural domains.")),
                    Paragraph(Text(
                        "For a cyclic five-row word of actual strict-band roots "
                        + "N_i=F(m)-b_i, the source's general row-indexed equations "
                        + "9.4-9.6 take h=m-1, e_i=4, delta_i=4-epsilon(m,b_i), "
                        + "and u_i=F(h-1)-b_i. Their parent and child parameters are "
                        + "A_i=F(h)-b_(i+1)-e_i, rho_i=F(h-2)-b_i+delta_i, "
                        + "sigma_i=F(h-3)-delta_i, "
                        + "alpha_i=F(h-1)-b_(i+1)+delta_(i+1)-e_i, and "
                        + "beta_i=F(h-2)-delta_(i+1), with cyclic indices. "
                        + "In the source row contract alpha_i+beta_i=A_i and "
                        + "beta_i=A_i-alpha_i. Both children retain the same row "
                        + "clock and natural child labels; the second parameters "
                        + "come from complementary subtraction. Repeated roots and "
                        + "shared physical children use the same C, g and d. "
                        + "These are substitutions into the source's general "
                        + "mechanics, not a Lean generic five-row closure theorem. "
                        + "The source H.6 cap-at-most-three interface is not used at "
                        + "deficit four. Pointwise producer identities are supplied "
                        + "by the present theorem, without independent phases, "
                        + "autonomous constant parameters or a uniform resource bound."))),
                DescribeRole.Theorem))));
}
