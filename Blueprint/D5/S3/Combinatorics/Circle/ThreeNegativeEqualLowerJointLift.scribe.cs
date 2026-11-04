using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeNegativeEqualLowerJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal lower gaps admit a joint physical lift",
        H("The entire equal-lower family"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-three-negative-equal-lower-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeNegativeEqualLowerJointLift.actualSource_three_negative_equal_lower_joint_lift"),
                H("One order and its literal ear for every 2<=b=c<a"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For all natural a,b,c with 2<=b, b=c and b<a, set k=a+b+c and u=1+2^a+2^(a+b). There exist one list sigma of all Fin(k) physical labels and one natural j<=k such that OriginalOrder(k,u,sigma) and OriginalOrder(k+1,2u,earWord(k,sigma,j)). Each order has complete integer sum zero and every natural take-prefix between zero and half its own modulus. The ear inserts the fresh physical label k at literal position j; every old label keeps its identity through castSucc. The physical length k is retained even when the numerical source has a shorter period.")),
                    Paragraph(Text("The case b=2 uses actualSource_three_negative_minimum_two_joint_lift. Otherwise write s=2^b>=8, m=s/2, h=2^(a-b), r=hs, N=hs^3-1 and C=(N-1)/2. Put B=1+s+sr and L=1+s+s^2. The actual positive chains U_i=i, V_i=b+i and W_i=2b+i have old/new pairs (u*2^i,2u*2^i), (B*2^i,(2B-1)*2^i), and (L*2^i,(2L-s-1)*2^i). Their lengths are b-1,b-1,a-1. The negative physical labels alpha=b-1,beta=2b-1,gamma=k-1 have old magnitudes H_alpha=(N-B)/2,H_beta=(N-L)/2,H_gamma=(N-u)/2. Their new magnitudes are 2H_alpha+1,2H_beta+m+1,2H_gamma+(u+1)/2. These paired identities and the fresh value u are supplied by the generic physical realization in ThreeNegativeMinimumTwoJointLift.")),
                    Paragraph(Text("For a<=2b-1, hence 2<=h<=m, take masks P=(0,m-1,h-1), T=(m-1,0,0), negative order (beta,gamma,alpha), and the ear immediately after beta. For a>=2b, write h=2H with H=2^(a-b-1)>=m. Take P=(1,m-2,H-1), T=(m-2,1,H), order (alpha,gamma,beta), and the ear immediately after alpha. These exponent alternatives cover every allowed a. The U/V split in the far branch exchanges their lowest bit: m-2 is even, so it is disjoint from the singleton mask 1. The W split uses the full low-bit mask H-1 and the single bit H, which are disjoint because H is a power of two. All six masks lie strictly below their physical capacities. In both branches Q is the physical complement of P,T and the three negative labels.")),
                    Paragraph(Text("The resulting old word is [P,pi1,Q,gamma,T,pi3], with fixed physical order within each positive block. The construction proves all eight canonical endpoint inequalities: H_pi1<=o(P)<=C, o(T)<=H_pi3, H_gamma+H_pi3-o(T)<=C; K_pi1<=n(P)<=N, n(T)<=K_pi3, K_gamma+K_pi3-n(T)<=N. The ear is Q. Every difference is an exact polynomial with nonnegative coefficients after using m-4 and h-2 (or m-h for the near upper bounds), and m-4 and H-m in the far branch. This proves unbounded integer inequalities without floors, residual search or an assumed feasible mask.")),
                    Paragraph(Text("More explicitly, set epsilon=o(P)-H_pi1, delta=H_pi3-o(T), A=2epsilon-q(P)-q_pi1 and D=2delta+q(T)+q_pi3. Near gives epsilon=(h-1)(s+1), delta=(h-1)s, A=(h-1)(s+1)-s, D=2(h-1)s+1. Far gives 2epsilon=h(3s+1)-s^2-4s-2, 2delta=h(3s-1)-s^2-4s, 2A=h(5s+1)-2s^2-7s, 2D=h(7s-1)-2s^2-7s+4. The endpoint proof includes epsilon in [0,C-H_pi1], delta>=0, A>=0 and D<=(u-1)/2. Complete physical inventory gives both integer totals, and positivity inside each block gives every internal prefix. The generic realize theorem converts these certificates to a single physical permutation and its identity-embedded ear.")),
                    Paragraph(Text("This is a repository construction in the study of Conjecture 3.1 of Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. It makes no literature novelty claim. It establishes exactly the entire equal-lower family; full Circle C3.1/J outside this family remains open."))),
                DescribeRole.Theorem)), []));
}
