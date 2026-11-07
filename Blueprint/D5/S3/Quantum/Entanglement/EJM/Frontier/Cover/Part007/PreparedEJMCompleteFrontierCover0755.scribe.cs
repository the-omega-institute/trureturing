using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0755Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0755.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0755",
        H("Original frontier context coverage 0755"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36243", "selected_cut_36243", "Selected cut at depth 12, code 288369, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 288369 returns the complete row with depth 12, base-four code 288369, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36290", "selected_cut_36290", "Selected cut at depth 11, code 72113, node 959759",
                "At remaining fuel 10 and original index 959759, selection on the full partial prefix of depth 11 and code 72113 returns the complete row with depth 11, base-four code 72113, original node 959759, kind 2, reserved field 0, 2377 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72092-958489", "unmarked_context_11_72092_958489", "Unmarked parent at depth 11, code 72092",
                "The frontier Boolean is false at remaining fuel 10, original node 958489, the whole prefixCache at depth 11 and code 72092, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4506-959657", "unmarked_context_9_4506_959657", "Unmarked parent at depth 9, code 4506",
                "The frontier Boolean is false at remaining fuel 12, original node 959657, the whole prefixCache at depth 9 and code 4506, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72092-958489", "node_context_11_72092_958489", "Original split at fuel 10 and node 958489",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 958410, 896706, 958447, 958488. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4506-959657", "node_context_9_4506_959657", "Original split at fuel 12 and node 959657",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 959119, 959333, 959484, 959656. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-288369-896706", "context_12_288369_896706", "Context at depth 12, code 288369, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 288369 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-72113-959759", "context_11_72113_959759", "Context at depth 11, code 72113, node 959759",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 72113 and original node 959759, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
