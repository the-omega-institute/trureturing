using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice.Orbifold;

internal sealed class P48qFixedRankCertificateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Lattice/Orbifold/P48qFixedRankCertificate.";
    private static readonly LibraryNoteRef Nebe = LibraryNoteRef.Create("D5/L/VertexAlgebra/nebe2014extremal48");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An exact integer matrix from the P48q lattice catalogue has cube one and both nonconstant traces zero. Its fixed space has dimension sixteen over every characteristic-zero field.",
        H("The P48q Order-Three Fixed-Rank Certificate"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nebe-order-three-matrix"),
                DeclarationHandle.Create(Prefix + "nebeOrderThree"),
                H("The integer row-action matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("M is the fourth power of the first generator in the Nebe–Sloane "
                    + "catalogue’s P48q entry. The exact entries form a matrix indexed by Fin 48 on both axes. "
                    + "The catalogue basis uses the row action x ↦ xM."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nebe-row-action"),
                DeclarationHandle.Create(Prefix + "rowAction"),
                H("The column-coordinate linear map"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("For a field K and an integer matrix A indexed by Fin 48 on both axes, "
                    + "transpose A, cast each entry to K, and use left matrix multiplication to act on K^48. "
                    + "This realizes the row-coordinate action x ↦ xA on column coordinates."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nebe-order-three-cube"),
                DeclarationHandle.Create(Prefix + "nebeOrderThree_cube"),
                H("The cube is the identity"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The integer matrix M satisfies M³ = I. A rowwise dot-product check "
                    + "proves that the square table is M². A second check multiplies that square by M and "
                    + "gives each row of the identity. List sums agree with the matrix multiplication sums."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nebe-order-three-trace"),
                DeclarationHandle.Create(Prefix + "nebeOrderThree_trace"),
                H("The trace of the matrix is zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The diagonal entries of M sum to zero over the integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nebe-order-three-square-trace"),
                DeclarationHandle.Create(Prefix + "nebeOrderThree_trace_square"),
                H("The trace of its square is zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(Paragraph(Text("The diagonal entries of the verified square M² sum to zero over the integers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nebe-order-three-fixed-rank"),
                DeclarationHandle.Create(Prefix + "nebeOrderThree_fixedRank16"),
                H("The fixed space has dimension sixteen"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Nebe),
                Blocks(
                    Paragraph(Text("For every characteristic-zero field K, write T for the linear map on "
                        + "K^48 with matrix Mᵀ after casting the entries to K. Then ker(T − I) has "
                        + "dimension sixteen over K.")),
                    Paragraph(Text("Transposition and the integer cast preserve the cube relation and the "
                        + "two traces. The powers I, T and T² define a representation of the cyclic group "
                        + "of order three whose invariant space is ker(T − I). The character average "
                        + "gives dimension (48 + 0 + 0)/3 = 16, in agreement with the fixed dimension "
                        + "in Table 2 of Nebe’s paper."))),
                DescribeRole.Theorem))));
}
