using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0548Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0548.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0548",
        H("Original frontier context coverage 0548"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-26307", "selected_cut_26307", "Selected cut at depth 12, code 88707, node 665467",
                "At remaining fuel 9 and original index 665467, selection on the full partial prefix of depth 12 and code 88707 returns the complete row with depth 12, base-four code 88707, original node 665467, kind 2, reserved field 0, 1617 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-26355", "selected_cut_26355", "Selected cut at depth 11, code 22191, node 666333",
                "At remaining fuel 10 and original index 666333, selection on the full partial prefix of depth 11 and code 22191 returns the complete row with depth 11, base-four code 22191, original node 666333, kind 2, reserved field 0, 3705 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-22176-665468", "unmarked_context_11_22176_665468", "Unmarked parent at depth 11, code 22176",
                "The frontier Boolean is false at remaining fuel 10, original node 665468, the whole prefixCache at depth 11 and code 22176, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-22188-666210", "unmarked_context_11_22188_666210", "Unmarked parent at depth 11, code 22188",
                "The frontier Boolean is false at remaining fuel 10, original node 666210, the whole prefixCache at depth 11 and code 22188, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-22176-665468", "node_context_11_22176_665468", "Original split at fuel 10 and node 665468",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 665402, 665425, 665447, 665467. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-22188-666210", "node_context_11_22188_666210", "Original split at fuel 10 and node 666210",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 666175, 666185, 666195, 666209. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-88707-665467", "context_12_88707_665467", "Context at depth 12, code 88707, node 665467",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 88707 and original node 665467, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-22191-666333", "context_11_22191_666333", "Context at depth 11, code 22191, node 666333",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 22191 and original node 666333, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
