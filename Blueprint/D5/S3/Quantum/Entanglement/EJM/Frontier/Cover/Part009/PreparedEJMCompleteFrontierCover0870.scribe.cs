using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0870Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0870.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0870",
        H("Original frontier context coverage 0870"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41763", "selected_cut_41763", "Selected cut at depth 12, code 336663, node 1141853",
                "At remaining fuel 9 and original index 1141853, selection on the full partial prefix of depth 12 and code 336663 returns the complete row with depth 12, base-four code 336663, original node 1141853, kind 2, reserved field 0, 3069 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41810", "selected_cut_41810", "Selected cut at depth 12, code 336713, node 1143030",
                "At remaining fuel 9 and original index 1143030, selection on the full partial prefix of depth 12 and code 336713 returns the complete row with depth 12, base-four code 336713, original node 1143030, kind 2, reserved field 0, 2041 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84165-1141854", "unmarked_context_11_84165_1141854", "Unmarked parent at depth 11, code 84165",
                "The frontier Boolean is false at remaining fuel 10, original node 1141854, the whole prefixCache at depth 11 and code 84165, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84177-1142954", "unmarked_context_11_84177_1142954", "Unmarked parent at depth 11, code 84177",
                "The frontier Boolean is false at remaining fuel 10, original node 1142954, the whole prefixCache at depth 11 and code 84177, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84165-1141854", "node_context_11_84165_1141854", "Original split at fuel 10 and node 1141854",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 308705, 1141795, 1141853. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84177-1142954", "node_context_11_84177_1142954", "Original split at fuel 10 and node 1142954",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1142898, 170504, 1142923, 1142953. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336663-1141853", "context_12_336663_1141853", "Context at depth 12, code 336663, node 1141853",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336663 and original node 1141853, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336713-1143030", "context_12_336713_1143030", "Context at depth 12, code 336713, node 1143030",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336713 and original node 1143030, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
