using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Raw.Part000.Raw014Checkpoints;

internal sealed class PreparedEJMCompleteFrontierRaw014Literal00Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Raw/Part000/Raw014Checkpoints/PreparedEJMCompleteFrontierRaw014Literal00.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact original Raw014 checkpoint Literal00",
        H("Exact original Raw014 checkpoint Literal00"),
        Blocks(
            Paragraph(Text("This checkpoint is consumed by the original Raw014 frontier facade and the original_score_lower_bound proof through its complete frontier dependency path.")),
            Paragraph(Text("All imports, namespaces, declarations, proofs and diagnostics are unchanged. Only the canonical production header is prepended. Metadata preparation does not establish acceptance of the new source bytes or the complete certificate.")),
            Node("accepted-d13-p18877-i60368", "accepted_d13_p18877_i60368", "Complete Accepted context at depth 13, prefix 18877 and node 60368",
                "The original Accepted proposition fixes depth 13, base-four prefix 18877 and literal DAG node 60368. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18880-i3444", "accepted_d13_p18880_i3444", "Complete Accepted context at depth 13, prefix 18880 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18880 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18884-i3444", "accepted_d13_p18884_i3444", "Complete Accepted context at depth 13, prefix 18884 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18884 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18888-i3444", "accepted_d13_p18888_i3444", "Complete Accepted context at depth 13, prefix 18888 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18888 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18892-i3444", "accepted_d13_p18892_i3444", "Complete Accepted context at depth 13, prefix 18892 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18892 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18896-i3444", "accepted_d13_p18896_i3444", "Complete Accepted context at depth 13, prefix 18896 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18896 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18900-i3444", "accepted_d13_p18900_i3444", "Complete Accepted context at depth 13, prefix 18900 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18900 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."),
            Node("accepted-d13-p18904-i3444", "accepted_d13_p18904_i3444", "Complete Accepted context at depth 13, prefix 18904 and node 3444",
                "The original Accepted proposition fixes depth 13, base-four prefix 18904 and literal DAG node 3444. It retains scale, fuel 8, the complete prefix cache and the complete partial assignment. Literal equality of a DAG node alone does not transfer acceptance to another prefix."))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
