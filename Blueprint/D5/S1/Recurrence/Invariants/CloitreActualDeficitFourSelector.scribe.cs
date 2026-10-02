using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualDeficitFourSelectorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A qualified actual deficit-four root has a unique canonical periodic selector with a complete quadratic enclosure.",
        H("Actual Cloitre Deficit-Four Selector"),
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
                DescribeId.Create("cloitre-actual-full30-3"),
                DeclarationHandle.Create("D5/S1/Recurrence/Invariants/CloitreActualDeficitFourSelector.full30_3"),
                H("Actual selection and first deficit-four hit"),
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
                        "For every natural m>=22 and b<=F(m-2) with exact parent "
                        + "qualification Q(m,b)=4, put N=F(m)-b, "
                        + "z=F(m-1)-g(N), w=F(m-2)-(N-g(N)), "
                        + "P=floor((m-2)^2/3)+30-3*m, Omega(r)=b-Q(m-1,r), "
                        + "and r0=b-4. The actual ordered routes are "
                        + "g(N)=F(m-1)-z and N-g(N)=F(m-2)-w, with z+w=b, "
                        + "z<=F(m-3) and w<=F(m-4). Their exact child deficits are "
                        + "Q(m-1,z)=4 and Q(m-2,w)=0, and w<=platformWidth(m-2), "
                        + "where platformWidth(k)=floor((2*k-9)/3). "
                        + "The signed integer jump g(N)-T(N,g(N)) is w-4. "
                        + "Each term is cast to the integers before subtraction.")),
                    Paragraph(Text(
                        "The complete quantitative enclosure is b<=4*P<=F(m-4). "
                        + "For every r<=b, both lower natural-block domains hold: "
                        + "r<=F(m-3) and r<=F(m-4). The corresponding physical point "
                        + "satisfies 1<=F(m-1)-r<=N-1. The full first lower profile "
                        + "satisfies Q(m-1,r)<=floor(2*r/3)<=b. Thus Omega(r)<=b "
                        + "and T(N,F(m-1)-r)=F(m-1)-Omega(r) on the entire interval.")),
                    Paragraph(Text(
                        "There exists a natural tau<=b with Q(m-1,Omega^tau(r0))=4 "
                        + "and Q(m-1,Omega^i(r0))!=4 for every i<tau. Its actual "
                        + "selected gap is z=Omega^tau(r0), its physical endpoint is "
                        + "g(N)=F(m-1)-Omega^tau(r0), and the minimal period of "
                        + "g(N) under this same actual T(N) is tau+1. For every r<=b "
                        + "that is periodic under Omega and satisfies Q(m-1,r)=4, "
                        + "r=Omega^tau(r0). This uniqueness ranges over every periodic "
                        + "gap in the interval, including distinct candidate cycles. "
                        + "The case tau=0 is included.")),
                    Paragraph(Text(
                        "The cap-three propagation starts from the two complete finite "
                        + "seeds. With Z(k)=3*k+floor((k-1)/3)-24 and W=Z(m-1), "
                        + "a qualified root lies either in b>=W+5 or at b=W+4 with "
                        + "m mod 3!=1. In the tail, periodic predecessors and the "
                        + "outside shelf force every first-child periodic deficit to "
                        + "be at least four; actual deficit addition then forces the "
                        + "selected pair (4,0). At the critical boundary, the prescribed "
                        + "absolute orbit alternates sides from its actual origin. "
                        + "Its depth F(m-1)-4 is odd, so the selected point is "
                        + "F(m-1)-W-1, giving z=W+1, w=3 and signed jump -1.")),
                    Paragraph(Text(
                        "The positive-cap budget uses P(9)=13 and "
                        + "P(k)=floor((k-2)^2/3)+30-3*k for k>=10. The complete "
                        + "gap lengths at orders nine and ten are thirteen and "
                        + "twenty-one, so positivity supplies the bases. Actual ordered "
                        + "child deficits add, zero child deficits use the existing "
                        + "platform zero set, and the budget recurrence yields "
                        + "v<=Q(k,v)*P(k) when Q(k,v)>0. Fibonacci domination gives "
                        + "4*P(m)<=F(m-4) for all m>=22.")),
                    Paragraph(Text(
                        "Bounded coordinate conjugacy identifies the gap and physical "
                        + "period predicates in both directions. The actual selected "
                        + "point is periodic and Omega(z)=r0, so r0 lies on that "
                        + "actual cycle. Injectivity on all periodic points makes z the "
                        + "unique periodic deficit-four gap. If its minimal period is p, "
                        + "the first hit from r0 is exactly p-1; the finite interval "
                        + "has b+1 points, so tau<=b. Coordinate injectivity is used "
                        + "only within the bounded legal interval.")),
                    Paragraph(Text(
                        "The exact parent qualification and the true full lower profile "
                        + "remain inputs. This finite walk does not acquire that "
                        + "qualification, identify an absolute clock-zero point of the "
                        + "orbit from N-1, or recover a transient entrance certificate. "
                        + "It needs no separate predecessor deficit, entrance clock, "
                        + "entrance point or phase label on this qualified domain. "
                        + "The profile-table size and walk length may grow with b; "
                        + "Fibonacci arithmetic and acquisition costs remain separate."))),
                DescribeRole.Theorem))));
}
