using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0601Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0601.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0601",
        H("Original frontier context coverage 0601"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-28852", "selected_cut_28852", "Selected cut at depth 12, code 93043, node 728234",
                "At remaining fuel 9 and original index 728234, selection on the full partial prefix of depth 12 and code 93043 returns the complete row with depth 12, base-four code 93043, original node 728234, kind 2, reserved field 0, 1609 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-28898", "selected_cut_28898", "Selected cut at depth 12, code 93197, node 390434",
                "At remaining fuel 9 and original index 390434, selection on the full partial prefix of depth 12 and code 93197 returns the complete row with depth 12, base-four code 93197, original node 390434, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-23260-728235", "unmarked_context_11_23260_728235", "Unmarked parent at depth 11, code 23260",
                "The frontier Boolean is false at remaining fuel 10, original node 728235, the whole prefixCache at depth 11 and code 23260, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-23298-730136", "unmarked_context_11_23298_730136", "Unmarked parent at depth 11, code 23298",
                "The frontier Boolean is false at remaining fuel 10, original node 730136, the whole prefixCache at depth 11 and code 23298, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-23260-728235", "node_context_11_23260_728235", "Original split at fuel 10 and node 728235",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 728117, 728174, 728209, 728234. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-23298-730136", "node_context_11_23298_730136", "Original split at fuel 10 and node 730136",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 448748, 729690, 729908, 730135. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-93043-728234", "context_12_93043_728234", "Context at depth 12, code 93043, node 728234",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93043 and original node 728234, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-93197-390434", "context_12_93197_390434", "Context at depth 12, code 93197, node 390434",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 93197 and original node 390434, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
