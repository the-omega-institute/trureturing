using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM;

internal sealed class EJMOriginalReplayAssemblyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/EJMOriginalReplayAssembly.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual prefix assembly of adaptive original suffixes",
        H("Actual prefix assembly of adaptive original suffixes"),
        Blocks(
            Paragraph(Text("Each suffix keeps its depth, base-four prefix, literal node, remaining fuel, complete cache and partial event. Leading zero outcomes retain their depth. Every adaptive internal node must be earned by an actual literal split and all four actual child receipts.")),
            Node("coordinate", "coordinate", "The next natural original coordinate",
                "At depths below twenty this is the original natural coordinate at that depth.", DescribeRole.Definition),
            Node("prefixCache", "prefixCache", "Compute the whole actual prefix cache",
                "The prefix is replayed from the actual original initial cache, using the last base-four digit for each actual coordinate update. All thirty-two states remain present.", DescribeRole.Definition),
            Node("prefixPartial", "prefixPartial", "Compute the same complete original partial event",
                "The same prefix digits and coordinates update the original partial assignment from the empty event.", DescribeRole.Definition),
            Node("Accepted", "Accepted", "Bind every actual suffix input",
                "The proposition checks the original DAG at fuel twenty-one minus depth with its literal node index, full computed cache and full computed partial assignment.", DescribeRole.Definition),
            Node("assemble", "assemble", "Assemble all four actual child suffixes",
                "Below depth twenty, the parent code and next outcome determine the exact child prefix. Literal split-node equality and all four complete child-context receipts imply the parent receipt. No shared shape alone transfers acceptance.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
