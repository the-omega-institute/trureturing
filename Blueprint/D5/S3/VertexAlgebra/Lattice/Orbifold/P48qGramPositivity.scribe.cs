using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qGramPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact triangular certificate proves positive definiteness of a symmetric integer matrix over the reals. The P48q catalogue Gram matrix satisfies the criterion.",
        H("Positive Definiteness of the P48q Gram Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("triangular-certificate-soundness"),
                DeclarationHandle.Create(Prefix + "posDef_intCast_of_triangular"),
                H("Soundness of the integer triangular certificate"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G and U be integer matrices indexed by any finite linearly ordered type. "
                        + "Suppose G is symmetric, U is upper triangular, GU is lower triangular, "
                        + "and the diagonals of U and GU are strictly positive.")),
                    Paragraph(Text("The matrix UᵀGU is lower triangular and symmetric, so it is diagonal. "
                        + "Only the diagonal summand contributes to its i-th diagonal entry, which is Uᵢᵢ(GU)ᵢᵢ > 0. "
                        + "Over the reals, U is invertible because its triangular determinant is nonzero. "
                        + "Mathlib's diagonal positivity and invertible congruence lemmas then give positive definiteness of the real cast of G."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("p48q-gram-posdef"),
                DeclarationHandle.Create(Prefix + "nebeGram_posDef"),
                H("The catalogue Gram matrix is positive definite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("The rank-48 integer Gram matrix G comes from P48qGramCertificate, whose lattice data supplies symmetry. "
                        + "The stored columns give an integer upper triangular matrix U with positive diagonal. "
                        + "Exact rowwise integer dot products establish that GU is lower triangular with positive diagonal. "
                        + "Applying the triangular criterion proves positive definiteness of the real form used in the P48q lattice data."))),
                DescribeRole.Theorem))));
}
