using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0527Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0527.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0527",
        H("Original frontier context coverage 0527"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 46 exact cut-selection equations, and 18 literal split equations paired with 18 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25301", "selected_cut_25301", "Selected cut at depth 11, code 19439, node 639724",
                "At remaining fuel 10 and original index 639724, selection on the full partial prefix of depth 11 and code 19439 returns the complete row with depth 11, base-four code 19439, original node 639724, kind 2, reserved field 0, 233 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25346", "selected_cut_25346", "Selected cut at depth 13, code 348251, node 641008",
                "At remaining fuel 8 and original index 641008, selection on the full partial prefix of depth 13 and code 348251 returns the complete row with depth 13, base-four code 348251, original node 641008, kind 2, reserved field 0, 1113 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-19438-639711", "unmarked_context_11_19438_639711", "Unmarked parent at depth 11, code 19438",
                "The frontier Boolean is false at remaining fuel 10, original node 639711, the whole prefixCache at depth 11 and code 19438, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-21764-640676", "unmarked_context_11_21764_640676", "Unmarked parent at depth 11, code 21764",
                "The frontier Boolean is false at remaining fuel 10, original node 640676, the whole prefixCache at depth 11 and code 21764, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-19438-639711", "node_context_11_19438_639711", "Original split at fuel 10 and node 639711",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 639668, 639685, 639697, 639710. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-21764-640676", "node_context_11_21764_640676", "Original split at fuel 10 and node 640676",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 307381, 640600, 640675, 893. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-19438-639711", "context_11_19438_639711", "Context at depth 11, code 19438, node 639711",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 19438 and original node 639711, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_77752_639668, context_12_77753_639685, context_12_77754_639697, context_12_77755_639710.", DescribeRole.Theorem),
            Node("context-13-348251-641008", "context_13_348251_641008", "Context at depth 13, code 348251, node 641008",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 348251 and original node 641008, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
