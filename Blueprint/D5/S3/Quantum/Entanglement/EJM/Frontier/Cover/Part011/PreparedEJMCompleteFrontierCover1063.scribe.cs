using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part011;

internal sealed class PreparedEJMCompleteFrontierCover1063Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part011/PreparedEJMCompleteFrontierCover1063.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 1063",
        H("Original frontier context coverage 1063"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-51028", "selected_cut_51028", "Selected cut at depth 11, code 114265, node 1465572",
                "At remaining fuel 10 and original index 1465572, selection on the full partial prefix of depth 11 and code 114265 returns the complete row with depth 11, base-four code 114265, original node 1465572, kind 2, reserved field 0, 2317 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-51076", "selected_cut_51076", "Selected cut at depth 11, code 114334, node 1467734",
                "At remaining fuel 10 and original index 1467734, selection on the full partial prefix of depth 11 and code 114334 returns the complete row with depth 11, base-four code 114334, original node 1467734, kind 2, reserved field 0, 1593 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-10-28566-1465620", "unmarked_context_10_28566_1465620", "Unmarked parent at depth 10, code 28566",
                "The frontier Boolean is false at remaining fuel 11, original node 1465620, the whole prefixCache at depth 10 and code 28566, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-28582-1467581", "unmarked_context_10_28582_1467581", "Unmarked parent at depth 10, code 28582",
                "The frontier Boolean is false at remaining fuel 11, original node 1467581, the whole prefixCache at depth 10 and code 28582, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-10-28566-1465620", "node_context_10_28566_1465620", "Original split at fuel 11 and node 1465620",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1465493, 1465572, 900587, 1465619. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-28582-1467581", "node_context_10_28582_1467581", "Original split at fuel 11 and node 1467581",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1467444, 1467530, 900587, 1467580. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-114265-1465572", "context_11_114265_1465572", "Context at depth 11, code 114265, node 1465572",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 114265 and original node 1465572, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-114334-1467734", "context_11_114334_1467734", "Context at depth 11, code 114334, node 1467734",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 114334 and original node 1467734, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
