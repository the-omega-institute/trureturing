using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaCoreProductDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaCoreProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual quotient E(X^3)^3/E(X) equals the complete core lattice theta at every coefficient.", H("CubicThetaCoreProduct"), Blocks(
            Paragraph(Text("The actual quotient E(X^3)^3/E(X) equals the complete core lattice theta at every coefficient.")),
            Node("0", "map_pentagonal", "Every commutative coefficient ring map preserves the actual pentagonal Euler series.", DescribeRole.Theorem),
            Node("1", "coreTheta_mul_euler", "The complete lattice theta times the actual Euler product is E(X^3)^3.", DescribeRole.Theorem),
            Node("2", "euler_constant_one", "The actual Euler product has constant coefficient one.", DescribeRole.Theorem),
            Node("3", "core_product_eq_theta", "This is the actual quotient, rather than a series defined to have nonnegative coefficients.", DescribeRole.Theorem),
            Node("4", "coeff_core_product", "Every normalized quotient coefficient counts the entire finite integer lattice fibre.", DescribeRole.Theorem),
            Node("extra-0", "root_equation", "The rational quadratic algebra contains a root of w squared plus w plus one.", DescribeRole.Theorem),
            Node("extra-1", "root_cube", "The chosen root has cube one.", DescribeRole.Theorem),
            Node("extra-2", "eval_T_one", "The actual Laurent evaluation maps index one to the algebraic root.", DescribeRole.Theorem),
            Node("extra-3", "eval_T_two", "The actual Laurent evaluation maps index two to the square of the root.", DescribeRole.Theorem),
            Node("extra-4", "eval_T_three", "The actual Laurent evaluation maps index three to one.", DescribeRole.Theorem),
            Paragraph(Text("These are attributed classical intermediate identities. CubicThetaIdentities proves the downstream Borwein relations and EtaSignK6 proves the exact all-index sign theorem. Independent formal acceptance and publication remain separate. No priority or unique claim is made."))
        ), []));
    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-core-product-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
