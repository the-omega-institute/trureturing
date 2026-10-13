using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class FiniteHeckeArrayDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bottom-up finite integer arrays compute the matrix of the actual prime Hecke operator, its integral lattice action and its integer characteristic polynomial.",
        H("Integer Array Hecke Algorithm"),
        Blocks(
            Paragraph(Text(
                "Let m>=1, let s belong to {0,4,6,8,10,14}, and let p be prime. The weight is k=12m+s. The input generators and Miller normalization are those of IntegralMillerBasis; the operator is the actual complex-linear primeHecke on Mathlib cusp forms. Matrices act on column coordinates, with row i equal to coefficient i+1 and column j equal to the j-th Miller form.")),
            Paragraph(Text(
                "rawMillerCoefficientArray computes a finite integer row from the existing divisor-sum and convolution algorithms. At descending depth d, millerDepthArrays appends row g_(m-1-d)(n)-sum_(ell<d) g_(m-1-d)(m-ell) B(ell,n), reading each previously materialized row from the table. The returned Array (Array Z) has one stored row per completed depth. No analytic coefficient evaluation, inverse basis equivalence or choice is executed by this algorithm.")),
            Describe.Lean(
                DescribeId.Create("miller-depth-arrays-correct"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.millerDepthArrays_correct"),
                H("Correctness of the materialized elimination table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For all natural m,s,N,d with m<N and d<=m, every stored row e<d has length N, and its entry at every n<N equals millerCoefficientDepth(m,s,e,n). The proof inducts on the table depth: old rows survive the push unchanged, while the new row agrees with the original integer recursion after applying the induction hypothesis to all earlier rows. This is a uniform algorithm invariant, including the empty table case."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-miller-hecke-matrix"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.integerMillerHeckeMatrix"),
                H("Executable integer Hecke matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Build the m rows once at length p*m+1. For zero-based i,j in Fin m, read the j-th Miller row at p*(i+1), and add p^(12*m+s-1) times its entry (i+1)/p when p divides i+1. The exponent and all arithmetic are natural or integer computations. Primality guarantees that every required index is strictly below p*m+1 and that the elimination coefficient indices are in range."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-hecke-matrix-analytic-map"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.integerMillerHeckeMatrix_map"),
                H("The integer array matrix represents the actual operator"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under p prime, m>=1 and the allowed residual-weight hypothesis, entrywise embedding of the computed integer matrix into C equals LinearMap.toMatrix of the actual primeHecke in the constructed integral Miller basis. The proof consumes the table invariant, every finite-index bound, the all-coefficient Miller bridge and the existing analytic Hecke coefficient law. It also proves the equality between the natural exponent k-1 used by the algorithm and the integer exponent used by the analytic action."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-hecke-coordinate-conjugacy"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.millerHecke_conjugacy"),
                H("Conjugacy in the actual first-coefficient coordinates"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every actual cusp form f at the stated weight, its first-m coefficient vector after applying primeHecke is the complex image of the computed integer matrix times its original first-m coefficient vector. This reuses Mathlib's toMatrix action law and is consumed by the full integral-lattice preservation proof."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("prime-hecke-full-integral-lattice"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/ModularForms/FiniteHeckeArray.primeHecke_integralCuspLattice"),
                H("Preservation of the entire integer coefficient lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every actual cusp form whose entire q-expansion has integer coefficients remains in that same lattice under primeHecke. Conjugacy expresses each of its first-m output coefficients as a finite integer linear combination of its integer lattice coordinates. The existing first-m integrality criterion then proves integrality of every coefficient. millerLatticeHecke consumes this theorem to restrict the actual operator to a Z-linear endomorphism of the full lattice."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "As an application of the matrix identification, the characteristic polynomial of the integer matrix belongs to Z[X], and its coefficientwise image in C[X] is the characteristic polynomial of the actual analytic primeHecke. This consequence reuses Matrix.charpoly_map and LinearMap.charpoly_toMatrix. It was checked as a transient Lean example, with no new named characteristic-polynomial theorem retained.")),
            Paragraph(Text(
                "Executable checks give the weight-12 T_2 matrix [[-24]] and the weight-24 T_2 matrix [[0,1],[20468736,1080]]. Evaluating the standard one- and two-dimensional determinant formulas gives ascending characteristic coefficients [24,1] and [-20468736,-1080,1], respectively. These executions check the delivered algorithm; no named positive finite-instance theorem is added. Mathlib's general charpoly definition remains noncomputable, so these checks do not provide a general executable characteristic-polynomial algorithm.")),
            Paragraph(Text(
                "This is a formal construction of classical level-one infrastructure. The analytic matrix and lattice theorems require the positive-dimensional Miller range stated above. No Maeda case, irreducibility theorem, characteristic-polynomial uniqueness result or mathematical originality is claimed.")))));
}
