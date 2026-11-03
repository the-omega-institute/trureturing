using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class CubicThetaRootProductEncodedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/ModularForms/CubicThetaRootProduct.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/huang2025signpatterns");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cubic root specialization of the actual Jacobi product", H("Cubic root specialization of the actual Jacobi product"), Blocks(
            Paragraph(Text("For any commutative topological ring and ring homomorphism out of the rational Laurent polynomial ring satisfying w^2+w+1=0 at its Laurent generator, the actual Jacobi series specializes to (1-w) times E(X^3). The root condition factors finite products and is not an assumed theta identity.")),
            Node("0", "finite_cubic_root_product", "An exact finite factorization, before any limit or division is taken.", DescribeRole.Theorem),
            Node("1", "jacobi_cubic_root_product", "Jacobi's actual formal product at a cubic root is (1-w)E(X^3). The algebraic root condition is used only to factor finite products.", DescribeRole.Theorem),
            Node("extra-0", "cubic_factor", "Three cubic-root polynomial factors multiply to one minus the cube, over any commutative ring.", DescribeRole.Theorem),
            Node("extra-1", "map_tendsto", "Discrete coefficient ring maps preserve coefficientwise power-series convergence.", DescribeRole.Theorem),
            Node("extra-2", "tendsto_expand_three", "Expansion by three preserves coefficientwise convergence.", DescribeRole.Theorem),
            Paragraph(Text("This is classical intermediate mathematics. CubicThetaCoreProduct supplies the downstream product-to-core lattice identity and EtaSignK6 supplies the exact all-index sign theorem. Independent formal acceptance and publication remain separate; no literature priority or novelty credit is asserted."))
        ), []));

    private static DocumentBlock Node(string id, string declaration, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("cubic-theta-root-product-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(declaration), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
}
