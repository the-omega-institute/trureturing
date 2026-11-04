using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.FiniteComponentClosure;

internal sealed class ModelsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Geometry/FiniteComponentClosure/Models.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate bouquets retain every positive-dimensional sphere occurrence and empty lists as points. Their finite disjoint unions model all nonempty finite component types. Native vertex gluing is identified with its actual quotient wedge.",
        H("Models"),
        Blocks(
            Paragraph(Text("Coordinate bouquets retain every positive-dimensional sphere occurrence and empty lists as points. Their finite disjoint unions model all nonempty finite component types. Native vertex gluing is identified with its actual quotient wedge.")),
            Node("bouquet-model", "bouquetComplex", "Finite positive-sphere bouquets",
                "A BouquetSpec is a finite list of positive sphere dimensions, counted with repetitions. Each native sphere is embedded with its selected vertex identified with one common coordinate vertex. The empty list is a single actual vertex and therefore one point component."),
            Node("bouquet-quotient", "bouquetQuotientHomeomorph", "The actual bouquet quotient",
                "The disjoint union of the finite sphere family and a separate common point, with precisely the repeated sphere basepoints and common point collapsed, is homeomorphic to the coordinate bouquet. The quotient kernel and surjectivity include the empty family."),
            Node("standard-bouquet", "standardBouquetHomeomorph", "Standard sphere quotient presentation",
                "The native finite bouquet is homeomorphic to the actual quotient bouquet of standard Euclidean spheres. Each sphere homeomorphism transports its specified basepoint, so this is an identification of actual quotient spaces."),
            Node("normal-model", "normalComplex", "All finite components",
                "The normal model is the tagged disjoint union of m coordinate bouquets. Different empty lists give different point components; no point component is deleted."),
            Node("normal-homeomorphism", "normalHomeomorph", "The tagged coproduct homeomorphism",
                "The coordinate realization of the normal complex is homeomorphic to the sigma type of its bouquet realizations, with their coproduct topology. The canonical normalPoint is the common vertex of the selected tagged bouquet."),
            Node("wplus", "WPlus", "Nonempty finite component homotopy types",
                "WPlus K means that the realization of K is homotopy equivalent to a normalComplex with a positive finite component count and a finite positive-sphere list for each component. Lists may be empty. This definition does not assert an arbitrary-index reduction."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
}
