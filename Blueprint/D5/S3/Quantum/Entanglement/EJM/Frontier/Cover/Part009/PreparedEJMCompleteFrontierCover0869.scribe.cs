using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0869Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0869.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0869",
        H("Original frontier context coverage 0869"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-41715", "selected_cut_41715", "Selected cut at depth 12, code 336498, node 1140345",
                "At remaining fuel 9 and original index 1140345, selection on the full partial prefix of depth 12 and code 336498 returns the complete row with depth 12, base-four code 336498, original node 1140345, kind 2, reserved field 0, 1209 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-41762", "selected_cut_41762", "Selected cut at depth 12, code 336662, node 1141795",
                "At remaining fuel 9 and original index 1141795, selection on the full partial prefix of depth 12 and code 336662 returns the complete row with depth 12, base-four code 336662, original node 1141795, kind 2, reserved field 0, 2929 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-84124-1140363", "unmarked_context_11_84124_1140363", "Unmarked parent at depth 11, code 84124",
                "The frontier Boolean is false at remaining fuel 10, original node 1140363, the whole prefixCache at depth 11 and code 84124, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-84164-1141738", "unmarked_context_11_84164_1141738", "Unmarked parent at depth 11, code 84164",
                "The frontier Boolean is false at remaining fuel 10, original node 1141738, the whole prefixCache at depth 11 and code 84164, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-84124-1140363", "node_context_11_84124_1140363", "Original split at fuel 10 and node 1140363",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1140320, 1140333, 1140345, 1140362. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-84164-1141738", "node_context_11_84164_1141738", "Original split at fuel 10 and node 1141738",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1108174, 1141650, 1141695, 1141737. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-336498-1140345", "context_12_336498_1140345", "Context at depth 12, code 336498, node 1140345",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336498 and original node 1140345, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-336662-1141795", "context_12_336662_1141795", "Context at depth 12, code 336662, node 1141795",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 336662 and original node 1141795, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
