using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1076Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1076.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1076",
        H("Original frontier context coverage 1076"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51651", "selected_cut_51651", "Selected cut at depth 12, code 1133346, node 1491931",
                "At remaining fuel 9 and original index 1491931, selection on the full partial prefix of depth 12 and code 1133346 returns the complete row with depth 12, base-four code 1133346, original node 1491931, kind 2, reserved field 0, 1469 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51697", "selected_cut_51697", "Selected cut at depth 10, code 71173, node 1468874",
                "At remaining fuel 11 and original index 1468874, selection on the full partial prefix of depth 10 and code 71173 returns the complete row with depth 10, base-four code 71173, original node 1468874, kind 1, reserved field 0, 1 subtree occurrences and completion domain 1048576. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-283336-1491963", "unmarked_context_11_283336_1491963", "Unmarked parent at depth 11, code 283336",
                "The frontier Boolean is false at remaining fuel 10, original node 1491963, the whole prefixCache at depth 11 and code 283336, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-17792-1493427", "unmarked_context_9_17792_1493427", "Unmarked parent at depth 9, code 17792",
                "The frontier Boolean is false at remaining fuel 12, original node 1493427, the whole prefixCache at depth 9 and code 17792, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-283336-1491963", "node_context_11_283336_1491963", "Original split at fuel 10 and node 1491963",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1469342, 1491855, 1491931, 1491962. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-17792-1493427", "node_context_9_17792_1493427", "Original split at fuel 12 and node 1493427",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1468246, 1493128, 1493290, 1493426. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-1133346-1491931", "context_12_1133346_1491931", "Context at depth 12, code 1133346, node 1491931",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 1133346 and original node 1491931, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-10-71173-1468874", "context_10_71173_1468874", "Context at depth 10, code 71173, node 1468874",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 71173 and original node 1468874, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
