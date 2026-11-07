using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.HardSplitCost;

internal sealed class NodeReceiptDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/HardSplitCost/NodeReceipt.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original prefix-aware hard-split NodeReceipt",
        H("Original prefix-aware hard-split NodeReceipt"),
        Blocks(
            Paragraph(Text("These source candidates preserve the original mathematical declarations and proof bodies. Metadata and Scribe preparation alone does not establish kernel acceptance, scoped-report acceptance, emission, complete producer acceptance or a global EJM score bound.")),
            Paragraph(Text("The source file determines declaration GIDs. Existing Lean namespaces and proof attribution are retained; an imported declaration is described by its actual source owner.")),
            Paragraph(Text("The existing HardSplitCost module path and TransientHardSplit namespace are retained. The mathematical source is reused from full-original-hard-split-prepare1; its existing terminal-confirmation.json records the earlier kernel comparison. Adding this header changes source bytes and has not been tested for cache reuse or recompiled here.")),
            Paragraph(Text("Raw002Tail442/Assembly.raw_cut_00337 consumes these exact declarations along the original parent context (depth 13, prefix 5209, node 17413). No benchmark runner, Direct module, old Child3 or old complete Assembled module is imported.")),
            Node("root-split-receipt", "root_split_receipt", "Original node 17413 split check",
                "At fuel eight, node 17413 checks against coordinate thirteen and the exact ordered child indices 17372, 17384, 17399 and 17412. The receipt supplies root_split."),
            Node("root-split", "root_split", "Exact split equation for original node 17413",
                "The checked split node is the actual original DAG node at fuel eight, coordinate thirteen and the same ordered four children. raw_cut_00337 uses this equation with all four complete child-context Accepted proofs."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
