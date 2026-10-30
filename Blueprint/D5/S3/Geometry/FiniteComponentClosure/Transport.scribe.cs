using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class TransportDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure/Transport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual continuous maps and inverse homotopies for joins, cone-base suspension homeomorphisms, Euclidean sphere models, and finite coordinate coproducts.",
        H("Transport"),
        Blocks(
            Paragraph(Text("Actual continuous maps and inverse homotopies for joins, cone-base suspension homeomorphisms, Euclidean sphere models, and finite coordinate coproducts.")),
            Node("sphere-model", "sphereComplex", "Native finite sphere models",
                "The zero-dimensional sphere is the complex of two distinct vertices. Higher sphere complexes are iterated simplicial joins with this two-point complex. Ghost ambient vertices are permitted; no unproved singleton face is added."),
            Node("sphere-homeomorphism", "sphereHomeomorph", "Actual Euclidean spheres",
                "For every natural dimension d, the coordinate realization of sphereComplex d is homeomorphic to the standard unit sphere in Euclidean space of dimension d+1. The base case is the explicit two-point homeomorphism; the induction uses the actual simplicial-join realization homeomorphism and the existing Euclidean sphere-join homeomorphism."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
