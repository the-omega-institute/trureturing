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
            Node("triangle-compose", "triangle_compose", "Exact composition on the whole triangle partial event",
                "Option-map composition and actual coordinate/outcome function equalities prove that applying t after s equals the recorded composed action on every coordinate.", DescribeRole.Theorem),
            Node("singleton-compose", "singleton_compose", "Exact composition on the whole singleton partial event",
                "This is the same symbolic whole-function proof for the actual singleton coordinate tables.", DescribeRole.Theorem),
            Node("triangle-update", "triangle_update", "Transport an actual triangle coordinate fill",
                "Injectivity and the actual right inverse show that a fill at i becomes a fill at the preimage of i, with its value transformed by the existing outcome action. Other coordinates retain the full old partial assignment.", DescribeRole.Theorem),
            Node("singleton-update", "singleton_update", "Transport an actual singleton coordinate fill",
                "The update proof uses the actual singleton inverse and outcome action. It applies to arbitrary partial assignments, with no normalization or producer premise.", DescribeRole.Theorem),
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
