using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualDeficitFourFeesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive fees on the full actual deficit-four support settle along the complete finite first-child spine.",
        H("Actual Cloitre Deficit-Four Positive Fees"),
        Blocks(
            Paragraph(Text(
                "F is the Fibonacci sequence with F(0)=0 and F(1)=1. Put "
                + "phi=(1+sqrt(5))/2 and G(n)=floor((n+1)/phi). The actual sequence "
                + "satisfies C(1)=C(2)=1. Its legal domain is D(N)=[1,N-1], its "
                + "inner map is T(N,x)=N-C(x), and X(N,i)=T(N)^i(N-1). "
                + "The depth is d(N)=C(N-1), g(N)=X(N,d(N)), and "
                + "C(N)=C(g(N))+C(N-g(N)) for N>=3. On the natural closed "
                + "block 0<=t<=F(m-2), put Q(m,t)=F(m-1)-C(F(m)-t). "
                + "The upper cap makes this an exact nonnegative integer difference. "
                + "All roots and descendants use this same C, g, d and T.")),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full30-5"),
                DeclarationHandle.Create("D5/S1/Recurrence/Invariants/CloitreActualDeficitFourFees.full30_5"),
                H("Full-support positive-fee partition and complete finite spine settlement"),
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
                        "Define Z(m)=3*m+floor((m-1)/3)-24, B(m)=4*m-34, and "
                        + "Phi(m,t)=max((t:Z)-(B(m):Z),0). Define "
                        + "K(N)=(g(N):Z)-(T(N,g(N)):Z), casting both terms before "
                        + "subtraction. Phi and K are signed integer expressions. "
                        + "For legal orders m>=21 the natural threshold B(m) agrees "
                        + "with the displayed subtraction. Define epsilon(m,b)=1 when "
                        + "b=Z(m)+1 and m mod 3!=1, and zero otherwise.")),
                    Paragraph(Text(
                        "For every m>=22 and legal gap b<=F(m-2) with Q(m,b)=4, "
                        + "put N=F(m)-b, z=F(m-1)-g(N), and "
                        + "w=F(m-2)-(N-g(N)). The actual child coordinates satisfy "
                        + "g(N)=F(m-1)-z, N-g(N)=F(m-2)-w, z+w=b, "
                        + "z<=F(m-3), and w<=F(m-4). Their deficits are "
                        + "Q(m-1,z)=4 and Q(m-2,w)=0. The signed identities are "
                        + "K(N)=w-4 and b-B(m)=(z-B(m-1))+K(N). The positive "
                        + "fee is exactly max(K(N),0)=Phi(m,b)-Phi(m-1,z).")),
                    Paragraph(Text(
                        "The low sector b<=B(m) satisfies Z(m)<b, z<=B(m-1), "
                        + "and K(N)<=0. Both potentials and the positive fee are zero. "
                        + "In its strict part b<B(m), the actual selected gaps are "
                        + "z=b-4+epsilon(m,b), w=4-epsilon(m,b), with "
                        + "K(N)=-epsilon(m,b) and z<B(m-1). Thus the exceptional "
                        + "epsilon=1 phase has complementary gap three. The separate "
                        + "endpoint b=B(m) has z=B(m-1), w=4 and K(N)=0.")),
                    Paragraph(Text(
                        "The high sector b>B(m) satisfies z>=B(m-1), K(N)>=0 "
                        + "and w>=4. When K(N)=0, z=b-4>B(m-1). When K(N)>0, "
                        + "there is a positive period p of the actual selected g(N) "
                        + "under this same T(N). Take y=T(N)^(p-1)(g(N)) and "
                        + "u=F(m-1)-y. Then T(N,y)=g(N), y belongs to D(N), "
                        + "y=F(m-1)-u, u<=F(m-3), and u<=b-4. This physical "
                        + "predecessor satisfies z=b-Q(m-1,u), Q(m-1,u)=w>=5, "
                        + "and u-w>=4*m-42. Consequently z>=B(m-1). The "
                        + "predecessor comes from the same selected cycle, without "
                        + "an independently chosen phase or preimage.")),
                    Paragraph(Text(
                        "For every M>=22 and legal deficit-four start b0, define "
                        + "N_s=g^s(F(M)-b0), m_s=M-s and b_s=F(m_s)-N_s. "
                        + "Then b_0=b0. Every node s<=M-21, including the terminal "
                        + "node, satisfies m_s>=21, N_s=F(m_s)-b_s, "
                        + "b_s<=F(m_s-2) and Q(m_s,b_s)=4. Every outgoing edge "
                        + "s<M-21 has m_s>=22 and N_(s+1)=g(N_s), "
                        + "m_(s+1)=m_s-1, b_(s+1)=F(m_s-1)-g(N_s). Its fee "
                        + "is Phi(m_s,b_s)-Phi(m_(s+1),b_(s+1)). The terminal "
                        + "order is exactly m_(M-21)=21.")),
                    Paragraph(Text(
                        "Put S=sum over s in {0,...,M-22} of max(K(N_s),0), "
                        + "equivalently the integer sum over range(M-21). The exact "
                        + "settlement is S=Phi(M,b0)-Phi(21,b_(M-21)). The "
                        + "terminal enclosure is b_(M-21)<=4*87=348, since "
                        + "P(21)=floor((21-2)^2/3)-3*21+30=87. With B(21)=50, "
                        + "0<=Phi(21,b_(M-21))<=298. Hence S>=0 and "
                        + "S<=Phi(M,b0)<=S+298. Also "
                        + "b0<=B(M)+Phi(M,b0)<=4*M+S+264.")),
                    Paragraph(Text(
                        "The terminal enclosure follows from positive integral "
                        + "defects on the closed blocks of lengths 13 and 21 at orders "
                        + "9 and 10, followed by the actual scalar child split through "
                        + "order 21. Put P(9)=13 and "
                        + "P(k)=floor((k-2)^2/3)-3*k+30 for 10<=k<=21. "
                        + "The zero child gaps lie on their proved platforms. The "
                        + "budget inequalities P(k)>=P(k-1)+platformWidth(k-2) "
                        + "and P(k)>=P(k-2)+platformWidth(k-1) yield "
                        + "v<=Q(k,v)*P(k) for positive defects. Applying this to "
                        + "the same terminal deficit-four root gives 348. The "
                        + "telescoping sum uses only outgoing orders at least 22.")),
                    Paragraph(Text(
                        "There exist uniform nonnegative real constants a,c with "
                        + "b<=a*m+c for every legal actual deficit-four root of every "
                        + "order m>=21 if and only if there exist uniform nonnegative "
                        + "real constants a',c' with S<=a'*M+c' for every complete "
                        + "actual deficit-four spine starting at M>=22. Forward, "
                        + "S<=Phi(M,b0)<=b0 preserves a,c. Reverse, "
                        + "a=a'+4 and c=c'+264 give the root bound; the order-21 "
                        + "case is absorbed because 4*21+264=348. This equivalence "
                        + "does not establish the existence of either bound. No "
                        + "interval description of the full support, quadratic "
                        + "attainment or infinite descending spine is asserted."))),
                DescribeRole.Theorem))));
}
