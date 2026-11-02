using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaCoreProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaCoreProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quotient E(X^3)^3/E(X) equals the complete core lattice theta at every coefficient.", H("CubicThetaCoreProduct"), Blocks(
            Paragraph(Text("The actual quotient E(X^3)^3/E(X) equals the complete core lattice theta at every coefficient.")),
            Node("0", "map_pentagonal", "Every rational coefficient ring map preserves the actual pentagonal Euler series.", DescribeRole.Theorem),
            Node("1", "coreTheta_mul_euler", "The complete core lattice theta times the actual Euler product equals E(X^3)^3. The proof evaluates the complete Jacobi cube in the quadratic algebra with w^2+w+1=0, compares actual finite product limits, and cancels a proven unit.", DescribeRole.Theorem),
            Node("2", "euler_constant_one", "The actual Euler product has constant coefficient one.", DescribeRole.Theorem),
            Node("3", "core_product_eq_theta", "The unit inverse quotient E(X^3)^3/E(X) is exactly the complete finite-fibre lattice theta.", DescribeRole.Theorem),
            Node("4", "coeff_core_product", "For every natural degree, including zero, the actual quotient coefficient is the cardinality of the entire finite integer fibre 3*(x^2+x*y+y^2)-2*x-y=n.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. The remaining Borwein identities and the complete original k6 sign theorem are separate obligations. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-core-product-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
