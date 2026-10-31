using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.HardSplitCost;

internal sealed class Child2Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/HardSplitCost/Child2.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original prefix-aware hard-split Child2",
        H("Original prefix-aware hard-split Child2"),
        Blocks(
            Paragraph(Text("These source candidates preserve the original mathematical declarations and proof bodies. Metadata and Scribe preparation alone does not establish kernel acceptance, scoped-report acceptance, emission, complete producer acceptance or a global EJM score bound.")),
            Paragraph(Text("The source file determines declaration GIDs. Existing Lean namespaces and proof attribution are retained; an imported declaration is described by its actual source owner.")),
            Paragraph(Text("The existing HardSplitCost module path and TransientHardSplit namespace are retained. The mathematical source is reused from full-original-hard-split-prepare1; its existing terminal-confirmation.json records the earlier kernel comparison. Adding this header changes source bytes and has not been tested for cache reuse or recompiled here.")),
            Paragraph(Text("Raw002Tail442/Assembly.raw_cut_00337 consumes these exact declarations along the original parent context (depth 13, prefix 5209, node 17413). No benchmark runner, Direct module, old Child3 or old complete Assembled module is imported.")),
            Node("child-2", "child_2", "Original complete-context acceptance: child_2",
                "Depth 14, base-four prefix 20838 and literal DAG node 17399 fix fuel 7, the complete prefix cache and the complete partial assignment. The conclusion is the original Accepted proposition at exactly these inputs."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
