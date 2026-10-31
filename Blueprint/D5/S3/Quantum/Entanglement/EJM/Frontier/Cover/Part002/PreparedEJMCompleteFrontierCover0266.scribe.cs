using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0266Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0266.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0266",
        H("Original frontier context coverage 0266"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-12770", "selected_cut_12770", "Selected cut at depth 13, code 105536, node 337078",
                "At remaining fuel 8 and original index 337078, selection on the full partial prefix of depth 13 and code 105536 returns the complete row with depth 13, base-four code 105536, original node 337078, kind 2, reserved field 0, 1589 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-12818", "selected_cut_12818", "Selected cut at depth 13, code 105584, node 338316",
                "At remaining fuel 8 and original index 338316, selection on the full partial prefix of depth 13 and code 105584 returns the complete row with depth 13, base-four code 105584, original node 338316, kind 2, reserved field 0, 1009 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26384-337124", "unmarked_context_12_26384_337124", "Unmarked parent at depth 12, code 26384",
                "The frontier Boolean is false at remaining fuel 9, original node 337124, the whole prefixCache at depth 12 and code 26384, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6598-338302", "unmarked_context_11_6598_338302", "Unmarked parent at depth 11, code 6598",
                "The frontier Boolean is false at remaining fuel 10, original node 338302, the whole prefixCache at depth 11 and code 6598, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26384-337124", "node_context_12_26384_337124", "Original split at fuel 9 and node 337124",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 337078, 337098, 337115, 337123. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6598-338302", "node_context_11_6598_338302", "Original split at fuel 10 and node 338302",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 338060, 338143, 338220, 338301. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-105536-337078", "context_13_105536_337078", "Context at depth 13, code 105536, node 337078",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105536 and original node 337078, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-105584-338316", "context_13_105584_338316", "Context at depth 13, code 105584, node 338316",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 105584 and original node 338316, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
