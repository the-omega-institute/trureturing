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
            Node("3", "hasSum_jacobi", "The actual normalized Jacobi product is the sum of all integer-index monomials.", DescribeRole.Theorem),
            Node("4", "hasSum_jacobi_cube", "The cube is the sum over all integer triples, with local finiteness proved before multiplying the sums.", DescribeRole.Theorem),
            Paragraph(Text("This classical intermediate does not prove the full original k6 Euler-quotient sign theorem. The cubic product-to-lattice identities remain separate obligations."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-jacobi-cube-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
