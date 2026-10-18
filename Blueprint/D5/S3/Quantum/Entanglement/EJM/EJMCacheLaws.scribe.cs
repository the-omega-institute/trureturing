using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCacheLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCacheLaws.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual local-action and block-projection laws",
        H("Actual local-action and block-projection laws"),
        Blocks(
            Paragraph(Text("Small finite kernel receipts check both inverse directions, coordinate multiplication, common-outcome composition and the original-block incidence tables. Symbolic function proofs then derive exact update and composition laws for arbitrary original partial assignments. The coordinate composition order is preserved rather than inferred from a producer tag. These laws are consumed by full cache association proofs.")),
            Node("triangle-injective", "triangle_coordinate_injective", "Triangle coordinate actions are injective",
                "Applying the checked inverse to equality of two transformed coordinates recovers equality of the original coordinates for every one of the twelve actual triangle permutations.", DescribeRole.Theorem),
            Node("singleton-injective", "singleton_coordinate_injective", "Singleton coordinate actions are injective",
                "The same inverse argument proves injectivity for all twelve actual singleton coordinate permutations.", DescribeRole.Theorem),
            Node("triangle-preimage", "triangle_preimage_apply", "The triangle preimage returns the original coordinate",
                "For every full local symmetry and triangle coordinate, applying its actual coordinate action to the recorded preimage returns that coordinate.", DescribeRole.Theorem),
            Node("singleton-preimage", "singleton_preimage_apply", "The singleton preimage returns the original coordinate",
                "The checked singleton right inverse supplies the exact coordinate recovery needed to transport arbitrary fills.", DescribeRole.Theorem),
            Node("triangle-compose", "triangle_compose", "Exact composition on the whole triangle partial event",
                "Option-map composition and actual coordinate/outcome function equalities prove that applying t after s equals the recorded composed action on every coordinate.", DescribeRole.Theorem),
            Node("singleton-compose", "singleton_compose", "Exact composition on the whole singleton partial event",
                "This is the same symbolic whole-function proof for the actual singleton coordinate tables.", DescribeRole.Theorem),
            Node("triangle-update", "triangle_update", "Transport an actual triangle coordinate fill",
                "Injectivity and the actual right inverse show that a fill at i becomes a fill at the preimage of i, with its value transformed by the existing outcome action. Other coordinates retain the full old partial assignment.", DescribeRole.Theorem),
            Node("singleton-update", "singleton_update", "Transport an actual singleton coordinate fill",
                "The update proof uses the actual singleton inverse and outcome action. It applies to arbitrary partial assignments, with no normalization or producer premise.", DescribeRole.Theorem),
            Node("triangle-unknown", "triangle_unknown", "Triangle actions preserve an unknown at its preimage",
                "If an original triangle partial assignment is unknown at a coordinate, the transformed assignment is unknown at its actual preimage. Exact coordinate recovery and Option.map prove this without restricting the other coordinates.", DescribeRole.Theorem),
            Node("singleton-unknown", "singleton_unknown", "Singleton actions preserve an unknown at its preimage",
                "Every unknown singleton coordinate remains unknown at its actual preimage under the full coordinate and outcome action.", DescribeRole.Theorem),
            Node("triangle-incidence", "triangle_incidence_some", "A triangle incidence names the actual global coordinate",
                "Whenever the original incidence table returns local coordinate i for global coordinate g and placement k, the actual triangle placement sends i to g.", DescribeRole.Theorem),
            Node("singleton-incidence", "singleton_incidence_some", "A singleton incidence names the actual global coordinate",
                "Every some-entry in the original singleton incidence table agrees with the actual singleton placement map.", DescribeRole.Theorem),
            Node("triangle-projection-update", "triangle_projection_update", "Exact change in an original triangle block",
                "A checked some-incidence and original block injectivity identify the single changed local coordinate. A checked none-incidence proves that the whole original projection is unchanged.", DescribeRole.Theorem),
            Node("singleton-projection-update", "singleton_projection_update", "Exact change in an original singleton block",
                "The actual singleton map receives the same complete projection proof, retaining every original coordinate and value.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
