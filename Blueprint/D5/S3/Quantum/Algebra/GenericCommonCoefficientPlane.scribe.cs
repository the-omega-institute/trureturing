using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class GenericCommonCoefficientPlaneDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An independent complex rectangular triple with injective stack above the strict three-halves threshold has one common neutral complex two-plane.",
        H("A simultaneous neutral coefficient plane"),
        Blocks(Describe.Lean(
            DescribeId.Create("generic-common-neutral-plane"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/GenericCommonCoefficientPlane.common_plane"),
            H("The entire Hermitian coefficient kernel"),
            StatementSource.FromLean(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For arbitrary natural dimensions a and b with 3a < 2b, let X be a complex-linearly " +
                    "independent triple of a-by-b matrices. Its stack Z has coefficient-first rows (r,i) " +
                    "and entries Z((r,i),j)=X(r)(i,j). If Z is injective, there is a complex submodule L " +
                    "of coefficient space of complex dimension two. For every Hermitian coefficient " +
                    "matrix T satisfying Z* (T tensor I_a) Z=0, the full sesquilinear pairing vanishes " +
                    "on every pair of vectors in this same L. The quantifiers include a zero kernel " +
                    "and every natural dimension; no nonzero form or signature is assumed.")),
                Paragraph(Text(
                    "Two product-rank inequalities force every coefficient-kernel matrix to have " +
                    "rank at most two. Independence excludes nonzero positive or negative semidefinite " +
                    "forms. A nonzero Hermitian form can therefore be put by invertible adjoint " +
                    "congruence into diag(1,-1,0). In these coefficients, equal column Grams give " +
                    "X(1)=U X(0) for a unitary U on the a-dimensional codomain.")),
                Paragraph(Text(
                    "Let D=range X(0) and R=X(2)(ker X(0)), with dimensions r and s. Stack injectivity " +
                    "gives r+s=b and s at most a, hence 2r>a. Restricting any kernel form to " +
                    "ker X(0) gives T(2,2)=0 and the cross relation (T(2,0)I+T(2,1)U)D orthogonal " +
                    "to R. For a nonzero cross pair, rank-nullity and the intersection dimension " +
                    "formula provide a nonzero v in D intersect R killed by this cross operator. " +
                    "Its second coefficient is nonzero, so v is a U-eigenvector. Pairing this same " +
                    "v against every kernel form gives one phase w with T(2,0)+w T(2,1)=0. " +
                    "A preimage of v under X(0) supplies the remaining neutral quadratic relation.")),
                Paragraph(Text(
                    "If all cross pairs vanish, put Q(T)=(T(0,0)+T(1,1))I+T(0,1)U+T(1,0)U*. " +
                    "The relation X(0)*Q(T)X(0)=0 and 2r>a make every Q(T) singular. Diagonalize " +
                    "the same U once. The resulting diagonal entries are real-linear functionals " +
                    "on the real vector space of Hermitian kernel forms. The finite-union theorem " +
                    "over the real field gives one diagonal coordinate vanishing on the whole " +
                    "kernel, and therefore a single phase for all its forms. In either branch, " +
                    "span{(0,0,1),(1,w,0)} is a common neutral complex plane. Invertible coefficient " +
                    "transport preserves its dimension and full pairing in the original coordinates."))),
            DescribeRole.Theorem))));
}
