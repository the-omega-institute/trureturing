using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class CanonicalCacheStateEqualityCandidateDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/CanonicalCacheStateEqualityCandidate.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Whole local-cache equality from complete State and canonical rows",
        H("Whole local-cache equality from complete State and canonical rows"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Paragraph(Text("The five public theorems are reusable equality and transition contracts. Each full-State premise retains the representative index and both action IDs, and each canonical-row premise retains all four MirrorRow fields. Locals consumes these contracts on the original literal inputs.")),
            Node("cachedLocal-eq-of-state-and-canonical-rows", "cachedLocal_eq_of_state_and_canonical_rows", "cachedLocal eq of state and canonical rows",
                "For any local-cache size, any mirror function and two local caches, the two full canonical-row equalities and equality of the entire State imply complete CachedLocal equality. The State includes the actual representative index and both action IDs; mere association supplies neither required premise.", DescribeRole.Theorem),
            Node("triangleStep-row-canonical", "triangleStep_row_canonical", "triangleStep row canonical",
                "For any triangle cache, local coordinate and outcome, the actual triangle transition constructs exactly the mirror row indexed by its resulting State. This is a full row equality and needs no separate association assumption.", DescribeRole.Theorem),
            Node("singletonStep-row-canonical", "singletonStep_row_canonical", "singletonStep row canonical",
                "For any singleton cache, local coordinate and outcome, the actual singleton transition constructs the full mirror row indexed by its resulting State.", DescribeRole.Theorem),
            Node("triangleStep-eq-of-state-and-mirror", "triangleStep_eq_of_state_and_mirror", "triangleStep eq of state and mirror",
                "For any actual and proposed triangle caches, local coordinate and outcome, equality of all three resulting State indices and equality of the proposed full row with the indexed canonical mirror imply equality of the entire actual transition output and proposal.", DescribeRole.Theorem),
            Node("singletonStep-eq-of-state-and-mirror", "singletonStep_eq_of_state_and_mirror", "singletonStep eq of state and mirror",
                "The singleton transition has the same complete equality contract: the entire resulting State and the full proposed canonical row are premises, and the conclusion is whole CachedLocal equality.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
