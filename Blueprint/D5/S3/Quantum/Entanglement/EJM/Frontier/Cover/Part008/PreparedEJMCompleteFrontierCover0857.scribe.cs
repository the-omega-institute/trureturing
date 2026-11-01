using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0857Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0857.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0857",
        H("Original frontier context coverage 0857"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41139", "selected_cut_41139", "Selected cut at depth 12, code 334356, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 334356 returns the complete row with depth 12, base-four code 334356, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41186", "selected_cut_41186", "Selected cut at depth 12, code 334406, node 1125616",
                "At remaining fuel 9 and original index 1125616, selection on the full partial prefix of depth 12 and code 334406 returns the complete row with depth 12, base-four code 334406, original node 1125616, kind 2, reserved field 0, 2545 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-83588-1123710", "unmarked_context_11_83588_1123710", "Unmarked parent at depth 11, code 83588",
                "The frontier Boolean is false at remaining fuel 10, original node 1123710, the whole prefixCache at depth 11 and code 83588, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-83600-1125546", "unmarked_context_11_83600_1125546", "Unmarked parent at depth 11, code 83600",
                "The frontier Boolean is false at remaining fuel 10, original node 1125546, the whole prefixCache at depth 11 and code 83600, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-83588-1123710", "node_context_11_83588_1123710", "Original split at fuel 10 and node 1123710",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1123536, 1123618, 1123709. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-83600-1125546", "node_context_11_83600_1125546", "Original split at fuel 10 and node 1125546",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1120586, 1125454, 1125499, 1125545. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-83588-1123710", "context_11_83588_1123710", "Context at depth 11, code 83588, node 1123710",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 83588 and original node 1123710, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_334352_1108174, context_12_334353_1123536, context_12_334354_1123618, context_12_334355_1123709.", DescribeRole.Theorem),
            Node("context-12-334406-1125616", "context_12_334406_1125616", "Context at depth 12, code 334406, node 1125616",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 334406 and original node 1125616, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
