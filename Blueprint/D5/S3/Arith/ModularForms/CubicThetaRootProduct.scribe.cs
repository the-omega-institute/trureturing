using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaRootProductEncodedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaRootProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic root specialization of the actual Jacobi product", H("Cubic root specialization of the actual Jacobi product"), Blocks(
            Paragraph(Text("For any commutative topological ring and ring homomorphism out of the rational Laurent polynomial ring satisfying w^2+w+1=0 at its Laurent generator, the actual Jacobi series specializes to (1-w) times E(X^3). The root condition factors finite products and is not an assumed theta identity.")),
            Node("0", "finite_cubic_root_product", "The three finite Jacobi factors collapse exactly to (1-w) times the finite Euler product at X cubed. No division or limiting argument occurs in this theorem.", DescribeRole.Theorem),
            Node("1", "jacobi_cubic_root_product", "Coefficientwise convergence of those finite factorizations proves the actual all-index formal product specialization.", DescribeRole.Theorem),
            Paragraph(Text("This is classical intermediate mathematics. The product-to-core lattice identity and the complete original k6 sign theorem are separate remaining obligations; no original-problem completion or novelty credit is asserted."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-root-product-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
