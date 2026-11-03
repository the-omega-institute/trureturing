using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaJacobiColumnsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaJacobiColumns.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Laurent column of the actual Jacobi cube is obtained from a complete integer-pair lattice sum. The index-zero column is the norm theta series; no product-to-core identity is assumed.", H("CubicThetaJacobiColumns"), Blocks(
            Paragraph(Text("Every Laurent column of the actual Jacobi cube is obtained from a complete integer-pair lattice sum. The index-zero column is the norm theta series; no product-to-core identity is assumed.")),
            Node("0", "cubeColumn", "The exact Laurent coefficient column of the actual normalized Jacobi cube.", DescribeRole.Definition),
            Node("1", "hasSum_cube_column", "Each Laurent column of the genuine cube is the full sum over two free integers.", DescribeRole.Theorem),
            Node("2", "triangular_zero_sum", "The zero-total triangular exponent is exactly Q(x,y).", DescribeRole.Theorem),
            Node("3", "triangular_one_sum", "The one-total triangular exponent is exactly Q(x,y)-x-y.", DescribeRole.Theorem),
            Node("4", "cube_column_zero", "The index-zero column of the actual Jacobi cube is the complete norm theta.", DescribeRole.Theorem),
            Node("one", "cube_column_one", "The index-one column includes all three affine cosets, with the exact negative sign.", DescribeRole.Theorem),
            Node("extra-0", "signs_add", "The three triangular monomial signs multiply to the sign of their full integer index sum.", DescribeRole.Theorem),
            Paragraph(Text("This classical intermediate supplies complete Jacobi columns. CubicThetaCoreProduct and CubicThetaIdentities prove the downstream product-to-lattice identities; EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-jacobi-columns-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
