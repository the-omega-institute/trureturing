using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part004;

internal sealed class PreparedEJMCompleteFrontierCover0409Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part004/PreparedEJMCompleteFrontierCover0409.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0409",
        H("Original frontier context coverage 0409"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-19635", "selected_cut_19635", "Selected cut at depth 13, code 289077, node 502270",
                "At remaining fuel 8 and original index 502270, selection on the full partial prefix of depth 13 and code 289077 returns the complete row with depth 13, base-four code 289077, original node 502270, kind 2, reserved field 0, 2081 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-19682", "selected_cut_19682", "Selected cut at depth 13, code 289136, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 289136 returns the complete row with depth 13, base-four code 289136, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-72269-502302", "unmarked_context_12_72269_502302", "Unmarked parent at depth 12, code 72269",
                "The frontier Boolean is false at remaining fuel 9, original node 502302, the whole prefixCache at depth 12 and code 72269, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-18070-503220", "unmarked_context_11_18070_503220", "Unmarked parent at depth 11, code 18070",
                "The frontier Boolean is false at remaining fuel 10, original node 503220, the whole prefixCache at depth 11 and code 18070, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-72269-502302", "node_context_12_72269_502302", "Original split at fuel 9 and node 502302",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 502270, 502290, 502301. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-18070-503220", "node_context_11_18070_503220", "Original split at fuel 10 and node 503220",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 502977, 503044, 503155, 503219. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-289077-502270", "context_13_289077_502270", "Context at depth 13, code 289077, node 502270",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289077 and original node 502270, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-289136-3444", "context_13_289136_3444", "Context at depth 13, code 289136, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 289136 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
