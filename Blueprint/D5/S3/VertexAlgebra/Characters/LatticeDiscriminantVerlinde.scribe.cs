using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Characters;

internal sealed class LatticeDiscriminantVerlindeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Characters/LatticeDiscriminantVerlinde.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite discriminant fusion convolution for the Weil S-kernel.",
        H("Finite Discriminant Verlinde Convolution"),
        Blocks(
            Definition("fusion-coefficient", "fusionCoefficient", "Normalized finite triple convolution",
                "For discriminant labels a, b and c, fusionCoefficient is the rho-normalized finite triple product of the pairing characters. It is the pointed finite modular-data analogue of a Verlinde coefficient."),
            Theorem("fusion-coefficient-indicator", "fusionCoefficient_eq_indicator", "Discriminant addition law",
                "The normalized Weil S convolution is exactly the indicator of the finite addition law a + b = c. The proof uses the nondegenerate pairing character orthogonality and rho squared equal to the discriminant cardinality."),
            Paragraph(Text("This is a finite modular-data identity for the lattice discriminant pairing. It does not assert a tensor-category construction or an analytic Verlinde theorem.")))));

    private static DocumentBlock Theorem(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static DocumentBlock Definition(string id, string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
