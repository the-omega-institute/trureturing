using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover1037Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover1037.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1037",
        H("Original frontier context coverage 1037"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-49780", "selected_cut_49780", "Selected cut at depth 12, code 409120, node 1108174",
                "At remaining fuel 9 and original index 1108174, selection on the full partial prefix of depth 12 and code 409120 returns the complete row with depth 12, base-four code 409120, original node 1108174, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-49827", "selected_cut_49827", "Selected cut at depth 12, code 409362, node 1413048",
                "At remaining fuel 9 and original index 1413048, selection on the full partial prefix of depth 12 and code 409362 returns the complete row with depth 12, base-four code 409362, original node 1413048, kind 2, reserved field 0, 2889 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-25569-1411231", "unmarked_context_10_25569_1411231", "Unmarked parent at depth 10, code 25569",
                "The frontier Boolean is false at remaining fuel 11, original node 1411231, the whole prefixCache at depth 10 and code 25569, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-8-1598-1412824", "unmarked_context_8_1598_1412824", "Unmarked parent at depth 8, code 1598",
                "The frontier Boolean is false at remaining fuel 13, original node 1412824, the whole prefixCache at depth 8 and code 1598, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-25569-1411231", "node_context_10_25569_1411231", "Original split at fuel 11 and node 1411231",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1410925, 1410994, 1411075, 1411230. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-8-1598-1412824", "node_context_8_1598_1412824", "Original split at fuel 13 and node 1412824",
                "The complete original decoder output is the split at coordinate 8, with value children 0 through 3 respectively at original indices 1411830, 1412380, 1412698, 1412823. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-10-25569-1411231", "context_10_25569_1411231", "Context at depth 10, code 25569, node 1411231",
                "The conclusion is adaptive Accepted at the exact depth 10, full base-four code 25569 and original node 1411231, hence remaining fuel 11, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_11_102276_1410925, context_11_102277_1410994, context_11_102278_1411075, context_11_102279_1411230.", DescribeRole.Theorem),
            Node("context-12-409362-1413048", "context_12_409362_1413048", "Context at depth 12, code 409362, node 1413048",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 409362 and original node 1413048, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
