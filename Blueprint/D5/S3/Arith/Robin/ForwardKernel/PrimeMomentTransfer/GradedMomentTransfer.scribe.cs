using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel.PrimeMomentTransfer;

internal sealed class GradedMomentTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/PrimeMomentTransfer/GradedMomentTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform finite-order error bound for the zero-degree collision terms.",
        H("Graded moment transfer"),
        Blocks(
            Paragraph(Text(
                "Let the index type be finite and A be a commutative real algebra, with ell:A->R real linear. "
                + "Suppose ell(1)=1, ell(Y(d))=0, and Y(d)^2=a*Y(d)+b*1. Let |f(i,d)|<=1. "
                + "Assume C>=1, H>=L>=1, card(index type)<=C*H and |a|,|b|<=C*L. "
                + "Write s=sqrt(H*L) and rho=sqrt(L/H). Require the bound |R_r(f_B1,...,f_Br)|<=C*s^r "
                + "for every 2<=r<k and pairwise disjoint nonempty label sets B1,...,Br within Fin k. "
                + "No bound on the top moment R_k is imposed, and no positivity or independence is required.")),
            Describe.Lean(DescribeId.Create("quadratic-moment-graded-transfer-bound"),
                DeclarationHandle.Create(Prefix + "quadratic_moment_graded_transfer_bound"),
                H("The zero-degree approximation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural order k and the data and hypotheses above, subtract from quadraticFamilyMoment(ell,Y,f) "
                    + "the sum over every partition sigma of Fin k and every retained subset S having singleton retained blocks "
                    + "and two-element unretained blocks, of partitionCoefficient(sigma,S,a,b)*partitionMainResidual(ell,Y,f,sigma,S). "
                    + "The absolute value of this difference is at most "
                    + "k^k*2^k*2^(k*k)*(C+1)^(k+1)*s^k*(rho+1/H). "
                    + "An unretained singleton kills its coefficient, and one retained block vanishes by centering. "
                    + "For the remaining configurations, delta=k-2*q-r is nonnegative. Positive delta gives the rho gain; "
                    + "at delta=0, removing a nonempty set of collision edges saves at least one free component and gives the 1/H gain. "
                    + "When there are no free blocks, the signed main residual is exact, so the top-order term is retained unchanged. "
                    + "There are at most k^k*2^k partition and retained-subset configurations and at most 2^(k*k) collision edge subsets."))),
                DescribeRole.Theorem))));
}
