using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw014Checkpoints;

internal sealed class PreparedEJMCompleteFrontierRaw014Literal04Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw014Checkpoints/PreparedEJMCompleteFrontierRaw014Literal04.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original Raw014 checkpoint Literal04",
        H("Exact original Raw014 checkpoint Literal04"),
        Blocks(
            Paragraph(Text("This checkpoint is consumed by the original Raw014 frontier facade and the original_score_lower_bound proof through its complete frontier dependency path.")),
            Paragraph(Text("All imports, namespaces, declarations, proofs and diagnostics are unchanged. Only the canonical production header is prepended. Metadata preparation does not establish acceptance of the new source bytes or the complete certificate.")),
            Node("accepted-d13-p18891-i60531", "accepted_d13_p18891_i60531", "Complete Accepted context at depth 13, prefix 18891 and node 60531",
                "The original Accepted proposition fixes depth 13, base-four prefix 18891 and literal DAG node 60531. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d14-p75519-i60163", "accepted_d14_p75519_i60163", "Complete Accepted context at depth 14, prefix 75519 and node 60163",
                "The original Accepted proposition fixes depth 14, base-four prefix 75519 and literal DAG node 60163. It retains scale, fuel 7, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
