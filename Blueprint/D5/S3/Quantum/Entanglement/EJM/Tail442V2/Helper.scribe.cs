using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2;

internal sealed class HelperDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/Helper.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full cache equality and the original node-442 replay connection",
        H("Full cache equality and the original node-442 replay connection"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Paragraph(Text("The existing Tail442V2.Helper source and namespace are retained. Generic whole-field equality and cache-checking lemmas coexist with the exact original node-442 and node-zero equations. Node equations alone do not prove any caller cache, lower inequality or prefix acceptance.")),
            Node("ReplayNode", "ReplayNode", "ReplayNode",
                "The original DAG node type retains its full global index space, twenty-coordinate input, four outcomes and original symmetry-cut type.", DescribeRole.Definition),
            Node("node442-split", "node442_split", "node442 split",
                "At remaining fuel three, original node 442 splits on original coordinate eighteen, with all four ordered child indices equal to original node zero. This is a node equation, not acceptance for any prefix.", DescribeRole.Theorem),
            Node("node0-bound", "node0_bound", "node0 bound",
                "At remaining fuel two, original node zero is a bound node. A caller must still supply its own entire cache and the lower inequality for that cache.", DescribeRole.Theorem),
            Node("FullLocalFields", "FullLocalFields", "FullLocalFields",
                "The relation requires equality of the complete State, consisting of the representative index and both action IDs, and equality of all four MirrorRow fields: hash, lower, slots and edges.", DescribeRole.Definition),
            Node("cachedLocal-eq-of-fields", "cachedLocal_eq_of_fields", "cachedLocal eq of fields",
                "For arbitrary local-cache size and actual and proposed CachedLocal values, equality of all FullLocalFields yields equality of the complete structures.", DescribeRole.Theorem),
            Node("fields-of-cachedLocal-eq", "fields_of_cachedLocal_eq", "fields of cachedLocal eq",
                "Complete CachedLocal equality supplies every FullLocalFields component. This transports a full equality; it does not infer one from hash, lower or association.", DescribeRole.Theorem),
            Node("step-at18-eq-of-local-fields", "step_at18_eq_of_local_fields", "step at18 eq of local fields",
                "For any entire cache, proposed entire next cache and outcome, complete field equalities at all sixteen triangle and all sixteen singleton placements imply the exact original coordinate-eighteen cache update. Incidence selects changed rows and retains every unaffected row.", DescribeRole.Theorem),
            Node("tail442", "tail442", "tail442",
                "For any entire cache, original partial assignment and four proposed entire child caches, four exact coordinate-eighteen step equalities and all four lower inequalities imply the original replay check at node 442 with fuel three. The partial assignment is retained; each caller earns its own cache and bounds.", DescribeRole.Theorem),
            Node("checkFullCache", "checkFullCache", "checkFullCache",
                "The Boolean guard checks complete State equality and all four MirrorRow fields at all sixteen triangle and sixteen singleton placements. No scalar or sorted-cache substitute is used.", DescribeRole.Definition),
            Node("cache-eq-of-checked", "cache_eq_of_checked", "cache eq of checked",
                "For any actual and proposed entire caches, a true checkFullCache receipt yields equality of the complete caches at every original placement.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
