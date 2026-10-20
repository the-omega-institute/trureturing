using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.KyFanGap;

internal sealed class NearExtremalDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Combinatorics/Graph/KyFanGap/NearExtremal.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An obstruction to simultaneous bilinear approximation and row concentration.",
        H("Approximation and row concentration"), Blocks(
            Describe.Lean(DescribeId.Create("kyfan-bilinear-approximation-gap"),
                DeclarationHandle.Create(Owner + "bilinear_approximation_gap"),
                H("A joint mean-square obstruction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Fix a nonsquare coordinate dimension k and a bound M on a bilinear kernel. There is a positive lower bound, uniform over sample size and coefficients, on the sum of two errors: the mean-square difference between the kernel matrix and a matrix with entries minus one or one, and the mean-square difference between that sign matrix's normalized row sums and 1/sqrt(k). The sign defect satisfies (H^2-1)^2 <= (M+1)^2(H-B)^2. Cauchy-Schwarz bounds the squared row-average approximation error by its mean-square entry error, and the square of a sum is at most twice the sum of the two squares. These inequalities bound the empirical polynomial defect by ((M+1)^2+2) times the first error plus twice the second. The positive empirical defect gap then gives the stated obstruction. Symmetry of the sign matrix is not needed."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("kyfan-uniform-gap"),
                DeclarationHandle.Create(Owner + "uniform_gap"),
                H("A uniform nonsquare Ky Fan gap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Eigenstructure/nikiforov2015extrema")),
                Blocks(Paragraph(Text("Every nonsquare positive integer k admits a positive gap below (1+sqrt(k))/2 for the normalized Ky Fan k-sum of every symmetric zero-one matrix of order at least k. Write c=1/sqrt(k), B=2A-J and T=B/n. An attaining signed orthonormal family defines Q=U diag(signs) U-transpose, with Q cubed equal to Q and squared Frobenius norm k. The two nonnegative variational deficits control both the Frobenius distance from T to cQ and the action of Q-I on the constant vector. Smooth the family by x(r,i)=sqrt(n)(T u(i))(r)/c. Cauchy-Schwarz bounds every coordinate by sqrt(k); the attaining family is supplied by the proved signed spectral formula. Its bilinear kernel satisfies H/n=TQT/c; the identity Q cubed equals Q bounds its approximation error by that of T-cQ. The same variational deficits bound the normalized row-sum error. Their sum would violate the positive bilinear approximation gap if the Ky Fan deficit were arbitrarily small. This produces a positive uniform gap without a numerical value for the optimal constant."))),
                DescribeRole.Theorem))));
}
