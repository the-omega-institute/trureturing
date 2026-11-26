using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qGramPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qGramPositivity.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The concrete P48q catalogue Gram matrix is positive definite over the reals.",
        H("Positive Definiteness of the P48q Gram Matrix"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("p48q-gram-posdef"),
                DeclarationHandle.Create(Prefix + "nebeGram_posDef"),
                H("The catalogue Gram matrix is positive definite"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("Let G be the rank-48 integer Gram matrix from P48qGramCertificate. Its existing lattice data supplies symmetry. The certificate gives an integral upper triangular matrix U with positive diagonal, and checks by exact rowwise integer dot products that GU is lower triangular with positive diagonal.")),
                    Paragraph(Text("Symmetry and triangularity give UᵀGU = diag(Uᵢᵢ(GU)ᵢᵢ). The diagonal is strictly positive. After casting to real matrices, U is invertible because its triangular determinant is nonzero, so positive definiteness transfers by congruence to the original real Gram matrix.")),
                    Paragraph(Text("This proves positivity of the actual form used in the P48q lattice data and supplies the positive form for the twisted construction."))),
                DescribeRole.Theorem))));
}
