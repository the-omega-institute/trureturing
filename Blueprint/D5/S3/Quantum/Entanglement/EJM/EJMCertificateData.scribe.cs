using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMCertificateDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMCertificateData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original EJM integer coefficient data and its earned local invariances.",
        H("The actual coefficient functions used by every certificate consumer"),
        Blocks(
            Paragraph(Text("The literal coefficient data comes from fast-inflation commit 01fcd357ee715dcff721f6a5381aedd2985c5696, data/ejm_224_nl_certificate.txt, SHA256 35c0221dea06ba6daf3f8d9a8e01914bc87eaabc8307491fe927173f9a94b20e. The ten-coordinate and nine-coordinate dictionaries contain 4588 and 1192 integer coefficients. CoefficientTree is an explicit binary dictionary with empty and key/value/left/right node constructors. A coefficient is attached to an entire equality-pattern and local-coordinate orbit with no orbit-size multiplier. The four exported invariance theorems concern these original lookup definitions. Merely defining the dictionaries supplies no coefficient amplitude, exact contraction receipt, positive inflation-score margin or nonlocality theorem. Each such numerical or actual-context acceptance obligation must be discharged by the corresponding kernel-checked consumer.")),
            Node("lookup", "get", "Original integer dictionary interpretation",
                "A matching key returns its stored integer. A smaller query descends left and a larger query descends right; an empty lookup returns zero. This executable interpretation is the original function used by later amplitude and contraction checks."),
            Node("pattern", "pattern", "The full equality-pattern code",
                "The code folds the equality test of every ordered coordinate pair into a natural number. Its definition retains the complete pairwise outcome equality relation; it does not enumerate an orbit or attach an orbit-size weight."),
            Node("triangle-permutations", "trianglePerm", "Twelve actual ten-coordinate maps",
                "The literal table gives the twelve local coordinate maps used by the triangle coefficient lookup. All subsequent orbit keys and symmetry proofs use this same table."),
            Node("singleton-permutations", "singletonPerm", "Twelve actual nine-coordinate maps",
                "The singleton coefficient lookup uses this literal twelve-map table in its original nine-coordinate order."),
            Node("orbit-key", "orbitKey", "The minimum equality-pattern code across the given local maps",
                "For an event and twelve supplied coordinate maps, the key is the finite minimum of their equality-pattern codes. This definition selects the dictionary query; it is not a positivity or amplitude certificate."),
            Node("triangle-multiplication", "triangleMul", "Composition indices for the actual triangle maps",
                "The explicit twelve-by-twelve table records the composition index used in the local-coordinate invariance proof. The private proof checks its relationship to the actual triangle coordinate functions."),
            Node("singleton-multiplication", "singletonMul", "Composition indices for the actual singleton maps",
                "The corresponding explicit composition table is used by the singleton coordinate invariance proof, together with the checked finite surjectivity of each multiplication row."),
            Node("triangle-data", "triangleCoefficients", "The complete original triangle coefficient dictionary",
                "The public tree assembles the literal 4588-entry original dictionary. Private parts organize the same tree; their presence is data storage, not proof that any score bound is valid."),
            Node("singleton-data", "singletonCoefficients", "The complete original singleton coefficient dictionary",
                "This public tree assembles the literal 1192-entry original singleton dictionary. Actual numerical consumers must use this interpretation and discharge their exact assertions about it."),
            Node("f1", "F1", "Original ten-coordinate integer coefficient function",
                "F1 queries triangleCoefficients at the original triangle orbit key of its ten-coordinate event. Missing dictionary keys return zero according to the same interpreter."),
            Node("f2", "F2", "Original nine-coordinate integer coefficient function",
                "F2 queries singletonCoefficients at the original singleton orbit key of its nine-coordinate event. The coefficient function itself contains no centered-score head sum or singleton factor 64."),
            Node("f1-relabel", "F1_relabel", "F1 is invariant under an injective common outcome map",
                "For every event and injective map of the four outcome labels, relabeling every coordinate preserves the original F1 value because it preserves every pairwise equality test.", DescribeRole.Theorem),
            Node("f2-relabel", "F2_relabel", "F2 is invariant under an injective common outcome map",
                "The same equality-pattern argument preserves the original F2 lookup under a common injective outcome relabeling.", DescribeRole.Theorem),
            Node("f1-coordinate", "F1_coordinate", "F1 is invariant under each actual local coordinate map",
                "The checked composition and surjectivity of the actual finite coordinate tables reindex the orbit-key minimum, preserving F1 under each of the twelve triangle maps.", DescribeRole.Theorem),
            Node("f2-coordinate", "F2_coordinate", "F2 is invariant under each actual local coordinate map",
                "The corresponding original singleton coordinate action preserves the orbit-key minimum and the actual F2 value. These invariances supply symmetry premises, not numerical score bounds.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
