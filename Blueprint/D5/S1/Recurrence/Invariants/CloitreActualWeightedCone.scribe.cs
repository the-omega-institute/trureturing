using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class CloitreActualWeightedConeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A weighted cone bounds every actual upper-anchor deficit at least five under the complete conditional source hypotheses.",
        H("Actual Cloitre Weighted Cone"),
        Blocks(
            Paragraph(Text(
                "F is the Fibonacci sequence with F(0)=0 and F(1)=1. C is the actual "
                + "positive-index Cloitre sequence with C(1)=C(2)=1. Its legal domain is "
                + "D(N)=[1,N-1], its inner map is T(N,x)=N-C(x), and its orbit X(N,i) "
                + "starts at N-1. The prescribed depth is d(N)=C(N-1), the selected "
                + "point is g(N)=X(N,d(N)), and C(N)=C(g(N))+C(N-g(N)) for N>=3. "
                + "Put Q(m,t)=F(m-1)-C(F(m)-t) on the full natural closed block "
                + "0<=t<=F(m-2). The upper cap makes Q the exact nonnegative integer "
                + "difference. It is distinct from the golden excess C(n)-G(n).")),
            Describe.Lean(
                DescribeId.Create("cloitre-actual-full30-6"),
                DeclarationHandle.Create("D5/S1/Recurrence/Invariants/CloitreActualWeightedCone.full30_6"),
                H("Weighted cone on every natural closed block"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every U satisfying Hyp24_1(U), retain its complete inherited "
                        + "Hyp21_1: the finite ratio condition 22877*C(n)<=15225*n for "
                        + "16384<=n<=131071; the full golden base and equality classification "
                        + "for 1<=n<=65535; and prescribed periodic entry for 3<=N<=52. "
                        + "The golden base states G(n)<=C(n), with equality implying "
                        + "n=F(j) or F(j)+1 for some j>=2, n+1=F(j) for an odd j>=3, "
                        + "or n in {11,24,25,59}. "
                        + "The global conditions include 1<=C(n), G(n)<=C(n)<=U(n)<=n, "
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
                        + "negative-collar invariance and capture for j>=6 and b<=F(j-1), "
                        + "and the full legal periodic intersection between "
                        + "max(F(j-1),F(j)-b) and min(F(j),F(j)+F(j-3)-b).")),
                    Paragraph(Text(
                        "Two additional finite full-block conditions are required. For every "
                        + "v<=F(18), Q(20,v)<=2 exactly when v<=35; when v>35, "
                        + "3<=Q(20,v)<=max(3,v-36). For every v<=F(19), "
                        + "Q(21,v)<=3 exactly when v<=45; when v>45, "
                        + "4<=Q(21,v)<=max(4,v-46). These conditions and the inherited "
                        + "foundations are premises; no instance of them is asserted.")),
                    Paragraph(Text(
                        "For all natural m>=21 and all 0<=t<=F(m-2), Q(m,t)>=5 implies "
                        + "t-(3/2)*Q(m,t)>=4*m-81 over the rationals. Multiplication by "
                        + "two gives the equivalent subtraction-free integer inequality "
                        + "3*Q(m,t)+8*m<=2*t+162.")),
                    Paragraph(Text(
                        "Let Z(m)=3*m+floor((m-1)/3)-24. Periodic predecessors and the "
                        + "finite order-twenty shelf give Q(21,v)=3 on v=42..45. "
                        + "An induction propagates Q(m,v)<=3 exactly on v<=Z(m), "
                        + "the exterior shelf, and the last four values equal to three. "
                        + "At the two-point boundary the adjacent actual row fixes the depth; "
                        + "exterior alternation from N-1 fixes its parity-selected phase.")),
                    Paragraph(Text(
                        "The golden estimate 8*Q(m,q)<=5*q+8 and the zero and exterior "
                        + "shelves prove q-(3/2)*Q(m,q)>=4 for every legal q>=4, "
                        + "using the ranges 4..11, 12..50, 51..87 and q>=88. Both "
                        + "orders twenty-one and twenty-two start the weighted induction. "
                        + "At higher orders the same actual children have inherited orders "
                        + "m-1,m-2 and legal gaps z,w with z+w=t. The cases are first "
                        + "deficit at least five, first deficit four with second deficit "
                        + "one through four, and first deficit four with second deficit "
                        + "at least five. No monotonicity of C, independent child choices, "
                        + "free periodic phase or limiting ratio is required."))),
                DescribeRole.Theorem))));
}
