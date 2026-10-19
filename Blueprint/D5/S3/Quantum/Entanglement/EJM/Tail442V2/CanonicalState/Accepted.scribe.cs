using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Tail442V2.CanonicalState;

internal sealed class AcceptedDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Tail442V2/CanonicalState/Accepted.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original acceptance at the complete prefix 5335038 and node 442",
        H("Original acceptance at the complete prefix 5335038 and node 442"),
        Blocks(
            Paragraph(Text("This document follows the actual source owner; the existing Lean namespace and all mathematical source are retained. Only already named public declarations receive Describe nodes. Private proofs, the anonymous instance and transient examples receive no new wrappers.")),
            Paragraph(Text("The production connection uses the complete original context at depth eighteen, base-four prefix 5335038 and node 442. Raw002Tail442/Assembly.raw_cut_00337 consumes that context along the original path from depth thirteen, prefix 5209 and node 17413. Its unchanged Raw002 response enters Responses110 and the original score lower-bound consumer.")),
            Paragraph(Text("Metadata preparation does not assert a successful compile, scoped report, Scribe emission, complete producer acceptance or global score bound. The other original sibling contexts and remaining producer components retain their separate proof obligations.")),
            Paragraph(Text("Parent.parent_exact supplies the separate full prefix-cache equality; Branch0 through Branch3 supply the four whole-cache steps and lower inequalities. The public accepted theorem retains its original exact type and is consumed once by the Raw002 five-split assembly. Other prefixes reaching node 442 remain separate contexts.")),
            Node("all-steps", "all_steps", "All steps",
                "For every one of the four outcomes, the original coordinate-eighteen step of the complete parentCache equals the corresponding complete nextCache. Each outcome uses its own branch step.", DescribeRole.Theorem),
            Node("all-bounds", "all_bounds", "All bounds",
                "For every outcome, the unchanged scale is at most the lower of its entire nextCache. The four branch inequalities are all retained.", DescribeRole.Theorem),
            Node("literal-context", "literal_context", "Literal context",
                "The original DAG replay check is true at fuel three, node 442, the entire literal parentCache and the original prefixPartial at depth eighteen and prefix 5335038. The proof consumes all_steps and all_bounds through Helper.tail442.", DescribeRole.Theorem),
            Node("accepted", "accepted", "Accepted",
                "The original EJMOriginalReplayAssembly.Accepted proposition holds at depth eighteen, prefix 5335038 and node 442. Parent.parent_exact connects the entire literal cache to the actual replayed prefix cache, and literal_context retains the full original partial assignment.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
