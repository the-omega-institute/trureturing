using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0144Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0144.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0144",
        H("Original frontier context coverage 0144"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-06915", "selected_cut_06915", "Selected cut at depth 13, code 88155, node 204460",
                "At remaining fuel 8 and original index 204460, selection on the full partial prefix of depth 13 and code 88155 returns the complete row with depth 13, base-four code 88155, original node 204460, kind 2, reserved field 0, 1161 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06962", "selected_cut_06962", "Selected cut at depth 13, code 88202, node 205390",
                "At remaining fuel 8 and original index 205390, selection on the full partial prefix of depth 13 and code 88202 returns the complete row with depth 13, base-four code 88202, original node 205390, kind 2, reserved field 0, 1049 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-22038-204461", "unmarked_context_12_22038_204461", "Unmarked parent at depth 12, code 22038",
                "The frontier Boolean is false at remaining fuel 9, original node 204461, the whole prefixCache at depth 12 and code 22038, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-22049-205340", "unmarked_context_12_22049_205340", "Unmarked parent at depth 12, code 22049",
                "The frontier Boolean is false at remaining fuel 9, original node 205340, the whole prefixCache at depth 12 and code 22049, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-22038-204461", "node_context_12_22038_204461", "Original split at fuel 9 and node 204461",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 204380, 204428, 204448, 204460. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-22049-205340", "node_context_12_22049_205340", "Original split at fuel 9 and node 205340",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 205284, 205313, 205331, 205339. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-88155-204460", "context_13_88155_204460", "Context at depth 13, code 88155, node 204460",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88155 and original node 204460, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-88202-205390", "context_13_88202_205390", "Context at depth 13, code 88202, node 205390",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 88202 and original node 205390, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
