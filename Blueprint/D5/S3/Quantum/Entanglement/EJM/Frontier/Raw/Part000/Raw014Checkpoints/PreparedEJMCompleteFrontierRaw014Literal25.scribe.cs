using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw014Checkpoints;

internal sealed class PreparedEJMCompleteFrontierRaw014Literal25Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw014Checkpoints/PreparedEJMCompleteFrontierRaw014Literal25.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original Raw014 checkpoint Literal25",
        H("Exact original Raw014 checkpoint Literal25"),
        Blocks(
            Paragraph(Text("This checkpoint is consumed by the original Raw014 frontier facade and the original_score_lower_bound proof through its complete frontier dependency path.")),
            Paragraph(Text("All imports, namespaces, declarations, proofs and diagnostics are unchanged. Only the canonical production header is prepended. Metadata preparation does not establish acceptance of the new source bytes or the complete certificate.")),
            Node("accepted-d14-p75576-i60552", "accepted_d14_p75576_i60552", "Complete Accepted context at depth 14, prefix 75576 and node 60552",
                "The original Accepted proposition fixes depth 14, base-four prefix 75576 and literal DAG node 60552. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d14-p75577-i60558", "accepted_d14_p75577_i60558", "Complete Accepted context at depth 14, prefix 75577 and node 60558",
                "The original Accepted proposition fixes depth 14, base-four prefix 75577 and literal DAG node 60558. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
