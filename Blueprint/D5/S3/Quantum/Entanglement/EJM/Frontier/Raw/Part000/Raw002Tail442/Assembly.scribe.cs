using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw002Tail442;

internal sealed class AssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw002Tail442/Assembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact five-split connection from Tail442 to original Raw002 cut 00337",
        H("Exact five-split connection from Tail442 to original Raw002 cut 00337"),
        Blocks(
            Paragraph(Text("The original depth-thirteen Raw337 statement is derived through five original split equations and the complete Accepted proposition at every child context.")),
            Paragraph(Text("The source file determines declaration GIDs. Existing Lean namespaces and proof attribution are retained; an imported declaration is described by its actual source owner.")),
            Paragraph(Text("The public theorem is the original raw_cut_00337 at depth thirteen, prefix 5209 and node 17413. Five exact original splits follow outcomes 3, 3, 3, 3, 2 to depth eighteen, prefix 5335038 and node 442. The complete Tail442V2/CanonicalState/Accepted.accepted result is consumed exactly once.")),
            Paragraph(Text("Every split requires its original node equation and all four complete child contexts. Three HardSplitCost children and ten unchanged Literal00 sibling proofs supply thirteen off-path children. Tail442V2/Prefix5335036/Accepted.accepted and Tail442V2/Prefix5335037/Accepted.accepted supply the other two at their own complete prefixes. The depth-seventeen assembly consumes them in outcomes zero and one, followed by the separate prefix-5335038 CanonicalState Accepted in outcome two and the original prefix-5335039 literal sibling in outcome three.")),
            Paragraph(Text("Raw002Shards/PreparedEJMCompleteFrontierRaw002Shard05 imports this module; the unchanged Raw002 facade derives response_cut_00337 from its original Raw name. Responses110 and the full response collection retain the path to the original score lower-bound consumer. Tail442 is a descendant of Raw002, not one of the Raw014 cuts.")),
            Node("raw-cut-00337", "raw_cut_00337", "Original complete-context acceptance: raw_cut_00337",
                "Depth 13, base-four prefix 5209 and literal DAG node 17413 fix fuel 8, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
