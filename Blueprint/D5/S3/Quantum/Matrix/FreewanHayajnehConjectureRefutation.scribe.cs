using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix;

internal sealed class FreewanHayajnehConjectureRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Matrix/FreewanHayajnehConjectureRefutation";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/freewanhayajneh2024geometricmean");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two sign-conjugate pairs of positive definite rational matrices reverse the proposed "
        + "operator-norm inequality at t=r=1/2, refuting Conjecture 2.",
        H("A counterexample to the weighted geometric mean norm comparison"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("freewan-hayajneh-conjecture-2"),
                DeclarationHandle.Create(Module + ".conjecture"),
                H("Conjecture 2 for every unitarily invariant norm"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text("For every dimension n and every nonempty finite family of "
                        + "positive definite complex n by n matrices A_i and B_i, every real "
                        + "t in [0,1], every real r with 1 at most 2r, every p>0, "
                        + "and every unitarily invariant norm N, the assertion is "
                        + "N(sum_i (A_i^2 #_t B_i^2)^r) at most "
                        + "N(((sum_i A_i)^((1-t)pr) (sum_i B_i)^(2tpr) "
                        + "(sum_i A_i)^((1-t)pr))^(1/p)).")),
                    Paragraph(Text("The weighted geometric mean is "
                        + "X #_t Y = X^(1/2) (X^(-1/2) Y X^(-1/2))^t X^(1/2). "
                        + "The existing weighted mean and real spectral power definitions "
                        + "are used. Every matrix, family-size, parameter and norm quantifier "
                        + "is retained; the counterexample uses n=m=2. The additional n=0 case has "
                        + "only the zero matrix, so every norm and both sides vanish."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("freewan-hayajneh-conjecture-2-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("Conjecture 2 is false"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("Take P=[[1,3/20],[3/20,9/4]], "
                        + "Q=[[1,1/5],[1/5,4/9]], and J=diag(1,-1). The two input pairs "
                        + "are (P,Q) and (JPJ,JQJ). Their positive leading principal minors "
                        + "prove positive definiteness. Choose t=r=1/2, p=2, and the "
                        + "Euclidean operator norm, which is unitarily invariant.")),
                    Paragraph(Text("The aggregate inputs are A=diag(2,9/2) and "
                        + "B=diag(2,8/9), with AB=4I. Diagonal functional calculus makes "
                        + "the right matrix 2I. Put z=1/100, X=97+135z-648z^2, "
                        + "Y=97-385z-648z^2, R=9409-27504z+46656z^2, u=sqrt(R), "
                        + "and v=sqrt((1-z)(1-9z)). The positive Riccati solution identifies "
                        + "C=P^2 #_(1/2) Q^2 with 1/u times the symmetric matrix whose "
                        + "diagonal entries are X,Y and whose off-diagonal entry is "
                        + "312(1/10)(1-3z). Its determinant is v^2.")),
                    Paragraph(Text("The positive square root is "
                        + "M=(C+vI)/w, where w=sqrt(tr(C)+2v). Write a=C_11 and c=C_22. "
                        + "Exact rational bounds give 95.59<u<95.60, 1.028<a<1.029, "
                        + "0.973<c<0.974 and 0.949<v<0.950. Squaring the positive root "
                        + "shows w<1.976, whereas a+v>1.977. Consequently "
                        + "M_11=(a+v)/w>1. Sign conjugation makes the left matrix M+JMJ, "
                        + "equal to 2 diag(M_11,M_22). Its operator norm is at least "
                        + "2M_11>2, strictly exceeding the right norm.")),
                    Paragraph(Text("The source case t=1/2, r at least one and pr at least "
                        + "one lies outside this counterexample. The assertion with r at "
                        + "least one and arbitrary p>0 remains undecided here. The general "
                        + "Conjecture 3 contains Conjecture 2 at s=2, so this counterexample "
                        + "gives a new s=2 counterexample; MI-21 uses s=1/2. "
                        + "The proof of Conjecture 1 is unaffected. Adding identity blocks "
                        + "extends the same mathematical construction to every dimension "
                        + "at least two. The stated negation uses only n=m=2 and p=2; "
                        + "the all-p identity and higher-dimensional extension are "
                        + "paper consequences, not additional kernel results. The parameter "
                        + "family 0<epsilon at most 1/10 is not formalized; the kernel proof "
                        + "uses only epsilon=1/10."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("freewan-hayajneh-2024-conjecture-2"),
                    ResolutionKind.Refuted)))));
}
