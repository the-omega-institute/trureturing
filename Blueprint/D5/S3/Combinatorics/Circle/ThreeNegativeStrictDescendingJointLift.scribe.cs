using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeNegativeStrictDescendingJointLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strict descending physical three-gap chamber",
        H("One physical permutation, with the ear immediately after gamma"),
        Blocks(
            Describe.Lean(DescribeId.Create("actual-source-three-negative-strict-descending-joint-lift"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/ThreeNegativeStrictDescendingJointLift.actualSource_three_negative_strict_descending_joint_lift"),
                H("Every natural a>b>c>=2"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Put k=a+b+c and v=1+2^a+2^(a+b). The conclusion gives one permutation sigma of every physical label in Fin(k), together with j<=k, for which both OriginalOrder(k,v,sigma) and OriginalOrder(k+1,2v,earWord(k,sigma,j)) hold. Both integer totals vanish, and every natural take-prefix lies between zero and half its own modulus. The new word inserts exactly the fresh physical label k into the identity embedding of sigma. No coprimality, minimal numerical period or rotation hypothesis is imposed.")),
                    Paragraph(Text("Write r=2^a,s=2^b,u=2^c,t=2^(b-c),m=2^(a-b-1),h=a-c-2,D=2^h. Then s=tu,r=4uD and 2D=mt. Here u is the smallest dyadic gap, while v denotes the seed. The positive physical chains are U_i=i,V_i=c+i,W_i=b+c+i, with lengths c-1,b-1,a-1. Their old coefficients are v,B=1+u+ur,L=1+s+su, and their new coefficients are 2v,2B-1,Lambda=2L-s-1. The actual negative labels alpha=c-1,beta=b+c-1,gamma=k-1 have the paired centered-source magnitudes furnished by the general paired-chain owner.")),
                    Paragraph(Text("The negative order is alpha,gamma,beta throughout. Let J be the W support used before gamma. If t<=2u, J={h,h+1} and its binary coefficient is w=3D. If t>=4u, J={0,...,h-1} union {h+1}, with w=3D-1. Dyadic separation makes these alternatives exhaustive. P1 contains every U label, a V mask p-1, and the single W label whose coefficient is e. P3 is the physical W complement of J and has coefficient q=r/2-1-w. P2 is the complement of P1 and P3 among the positive physical labels. Thus sigma=[P1,alpha,P2,gamma,P3,beta], and the new word is [P1,alpha,P2,gamma,k,P3,beta]. The existing mask realizer proves complete physical inventory, all prefixes, and this literal ear identity.")),
                    Paragraph(Text("The five exhaustive choices of (p,e) are (2,D) for t=2; (2,2D) for t=4; (3t/4,D) for 8<=t<=2u; (t,m) for t>=4u,m>=2; and (t-1,2) for t>=4u,m=1. Their V supports are respectively {0}, {0}, {0,...,d-3} union {d-1}, {0,...,d-1}, and {1,...,d-1}, where d=b-c. The chosen W index is respectively h,h+1,h,ell,1, with ell=a-b-1. Each selected bit belongs to J and is disjoint from its physical complement; the chain capacities are checked for all exponents, including c=2.")),
                    Paragraph(Text("After alpha the old and new landings are z=pB-v+eL and zhat=2z-p-(s+1)e. The five branches establish z<=(B-1)/2 and zhat>=0. After gamma, before the ear, they are y=wL+(L-v)/2 and yhat=wLambda+L-s/2-(3v+1)/2. The numerator is 3v+1. The two W supports satisfy y<=(v-1)/2 and yhat>=0. Before the ear, each old label has new value twice its old value minus a nonnegative defect: zero on U,2^i on V,(s+1)2^i on W, and 1,s/2+1,(v+1)/2 on alpha,beta,gamma. These asymmetric defects turn old upper bounds into new upper bounds; the new lower bounds require the separate landing estimates.")),
                    Paragraph(Text("The tail identities y+qL=H_beta and yhat+v+qLambda=K_beta place the ear and all remaining positive W prefixes below their final negative magnitudes, and beta returns both paths to zero. The cut is literally after gamma: counting the displayed supports gives b+c+2 in the near regime and a+b-1 in the far regime. The endpoint theorem retains the existential literal cut proved by the physical scheduler. This is a repository-derived construction in the strict descending chamber of the Circle joint-permutation problem, motivated by Damasdi, Frankl, Pach and Palvolgyi, Monochromatic configurations on a circle, arXiv:2504.10687v2. It makes no external novelty claim. Full physical J and full Circle C3.1 remain open."))),
                DescribeRole.Theorem)), []));
}
