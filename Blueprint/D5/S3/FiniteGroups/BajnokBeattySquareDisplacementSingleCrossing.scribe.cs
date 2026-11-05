using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class BajnokBeattySquareDisplacementSingleCrossingDocument
    : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bajnokbeatty2024cayleydiameteroriginal");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact finite signed-word returns have a unique first-wrap threshold for every odd square displacement.",
        H("The all-odd square-displacement threshold"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("square-displacement-actual-return-pair"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattySquareDisplacementSingleCrossing.square_return_pair"),
                H("The two actual return counts"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every integer p, integer q and natural t, let Plane be the integer plane, m=2qt-1 and n=(p*m).toNat. Put v1a=(p(m-1)/2,p(m+1)/2), v2a=(p(m-q^2)/2,-p(m+q^2)/2), v1q=(p(m-q)/2,p(m+q)/2), and v2q=(p(m-q)/2,-p(m+q)/2). Every displayed division in these coordinates is integer division. Let Ka and Kq be the complete integer spans of the respective two vectors, and let Fa:Plane -> Plane/Ka and Fq:Plane -> Plane/Kq be the quotient homomorphisms. The definition square_return_pair p q t is (W(Fa,n),W(Fq,n)).")),
                    Paragraph(Text("Here W(F,n) is the cardinality of all signed coordinate words w:Fin n -> Fin 4 whose integer endpoint maps to zero under F. The four letters are the positive and negative coordinate steps. No truncated kernel, binomial sequence, endpoint classification premise or comparison premise is part of this definition."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("square-displacement-single-crossing"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/BajnokBeattySquareDisplacementSingleCrossing.actual_square_displacement_single_crossing"),
                H("The unique threshold and its finite upper bound"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("For every integer p with 3<=p and Odd p, and every integer q with 3<=q and Odd q, put tmin=((q+1)/2).toNat and tlate=((q*p+1)/2).toNat. There exists exactly one natural T satisfying all five conditions: tmin<T; for every natural t with tmin<=t<T the second component of square_return_pair p q t is strictly smaller than the first; at t=T the first component is at most the second; for every natural t with T<t the first component is strictly smaller than the second; and T<=tlate. All natural t>=tmin and all odd composites are retained, including p=3 and q=3.")),
                    Paragraph(Text("Set a=qpt, r=(q-1)p/2, l=(q^2-1)p/2, A=choose(n,a), B=choose(n,a+r), D=choose(n,a+l). In this admissible range m>q^2, every index fits, and the existing asymmetric_rank_one_actual_data and odd_boundary_count_of_sumDiff give exactly Wa=2(A+D) and Wq=4B for the complete quotient walks. This uses the established endpoint classification unchanged.")),
                    Paragraph(Text("For the finite recurrence put K(M,j)=choose(2M+1,M-j), S(M)=(M+1)(M+2), lambda(j)=j(j+1), j0=(p-1)/2, j1=(qp-1)/2 and j2=(q^2*p-1)/2. Let h=(q^2-1)p^2/4 and c=q^2+1. The exact lambda gaps are h and c*h. On every row M=j2+z, z natural, Q=S(M)-lambda(j0)>c*h, x=K(M,j1)/K(M,j0)>0 and y=K(M,j2)/K(M,j0)>0. The existing exact two-row ratio recurrence yields xnext=xQ/(Q-h) and ynext=yQ/(Q-c*h). The free factor c=q^2+1 replaces the factor 10 of the q=3 case.")),
                    Paragraph(Text("The new algebra proves dx=xnext-x>0, strict increase of y/x, and dnext-d=dx*(2-c*ynext/xnext) for d=2x-1-y. The existing finite_sign_persistence applies unchanged: increasing slopes and a later positive finite sample beyond every row index make every nonnegative d strictly positive at all later indices. Actual t-values give an increasing unbounded subsequence M=(p(2qt-1)-1)/2. Binomial symmetry identifies Wq-Wa=2K(M,j0)d, whose factor is positive.")),
                    Paragraph(Text("The cofinal samples follow from finite adjacent drops. With n+p=2a and c(k)=choose(n,k), sum the exact identity (c(k)-c(k+1))(k+1)=c(k)(2k+1-n) over a first block of length r and a second block of length q*r. Monotonicity on the decreasing half-row gives A*(a-h)<=B*a and D*(a+l+q^2*h)<=B*(a+l). For u=a-h and v=a+l+q^2*h, the condition 2a>p+q^2*p^2 makes u and v positive. The surplus 2uv-a*v-(a+l)*u equals h*((q^2-1)*a-l-2q^2*h), equivalently ((q^2-1)^2*p^2/8)*(2a-p-q^2*p^2), and is positive. Multiplying the weighted bounds proves A+D<2B. Every t>=tlate satisfies this sufficient condition. For each row index the proof explicitly chooses a sufficiently large actual natural t; no cofinality premise is assumed.")),
                    Paragraph(Text("At tmin, n0=p(q^2+q-1) and R=n0+1. The finite centered product gives A/B as the product over i<r of (1+x_i)/(1-x_i), where x_i=(p+2i+1)/R lies strictly between zero and one. The existing sum_linear gives 2 sum x_i=(q^2-1)p^2/(2R). The polynomial F=(q^2-1)p^2-2p(q^2+q-1)-2 is positive: F(3,q)=3(q-1)^2-8>=4, and F(p,q)-F(3,q)=(p-3)*((p+1)*(q^2-1)-2q)>=0. Thus 2 sum x_i>=1. Each factor is 1+2x_i/(1-x_i); the finite product lower bound and strict inequality 2x_i/(1-x_i)>2x_i on the nonempty range imply A/B>2. Consequently Wq<Wa initially. The least nonnegative count difference, constructed with Nat.find above this variable baseline, gives the threshold; persistence gives all strict later signs and uniqueness, and the late sign gives T<=tlate.")),
                    Paragraph(Text("These are the same square-displacement quotients as in same_group_square_displacement_growth. With Dgroup=(m^2-q^2)/2 their underlying noncyclic group is ZMod(p.natAbs) times ZMod((p*Dgroup).natAbs), while the coordinate markings differ and their signed-ball growth profiles differ. The present return-count result adds a unique first-wrap sign threshold for each p,q. It asserts neither equality at the threshold nor universal spectral ordering, corrected q-family rounding, a Gaussian limit, or a continuous binomial identity.")),
                    Paragraph(Text("The lattice and extremal-growth setting follows the Bajnok-Beatty line already represented by the surrounding sources. The exact counting, generic binomial recurrence, adjacent-drop sums and centered finite product are reused from the named repository results; the free-factor algebra and all-q finite initial and late comparisons supply the extension. No literature-novelty claim is made."))),
                DescribeRole.Theorem))));
}
