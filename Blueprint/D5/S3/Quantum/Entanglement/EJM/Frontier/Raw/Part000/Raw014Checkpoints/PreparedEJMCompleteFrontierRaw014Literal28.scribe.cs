using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw014Checkpoints;

internal sealed class PreparedEJMCompleteFrontierRaw014Literal28Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw014Checkpoints/PreparedEJMCompleteFrontierRaw014Literal28.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original Raw014 checkpoint Literal28",
        H("Exact original Raw014 checkpoint Literal28"),
        Blocks(
            Paragraph(Text("This checkpoint is consumed by the original Raw014 frontier facade and the original_score_lower_bound proof through its complete frontier dependency path.")),
            Paragraph(Text("All imports, namespaces, declarations, proofs and diagnostics are unchanged. Only the canonical production header is prepended. Metadata preparation does not establish acceptance of the new source bytes or the complete certificate.")),
            Node("accepted-d14-p75515-i60392", "accepted_d14_p75515_i60392", "Complete Accepted context at depth 14, prefix 75515 and node 60392",
                "The original Accepted proposition fixes depth 14, base-four prefix 75515 and literal DAG node 60392. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d14-p75595-i60620", "accepted_d14_p75595_i60620", "Complete Accepted context at depth 14, prefix 75595 and node 60620",
                "The original Accepted proposition fixes depth 14, base-four prefix 75595 and literal DAG node 60620. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
