using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaJacobiCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaJacobiCube.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Locally finite integer sums realize the actual Jacobi series and its cube. Triangular exponent bounds justify the full Cauchy products, including every integer index.", H("CubicThetaJacobiCube"), Blocks(
            Paragraph(Text("Locally finite integer sums realize the actual Jacobi series and its cube. Triangular exponent bounds justify the full Cauchy products, including every integer index.")),
            Node("0", "twice_triangular", "The natural triangular exponent has twice its value equal to k(k-1) for every integer k.", DescribeRole.Theorem),
            Node("1", "triangular_bound", "A bound on the triangular exponent bounds the integer index in an explicit finite interval.", DescribeRole.Theorem),
            Node("2", "jacobiTerm", "The signed triangular monomial at the integer Laurent index.", DescribeRole.Definition),
            Node("3", "hasSum_jacobi", "The genuine normalized product is the locally finite sum over every integer index.", DescribeRole.Theorem),
            Node("4", "hasSum_jacobi_cube", "The cube includes all triples; local finiteness justifies the Cauchy products.", DescribeRole.Theorem),
            Node("extra-0", "hasSum_map_jacobi", "Coefficient maps preserve the complete locally finite Jacobi sum.", DescribeRole.Theorem),
            Node("extra-1", "hasSum_mapped_triple", "Distinct coefficient evaluations retain every triple in the Cauchy product.", DescribeRole.Theorem),
            Paragraph(Text("This classical intermediate supplies complete Jacobi columns. CubicThetaCoreProduct and CubicThetaIdentities prove the downstream product-to-lattice identities; EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-jacobi-cube-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
