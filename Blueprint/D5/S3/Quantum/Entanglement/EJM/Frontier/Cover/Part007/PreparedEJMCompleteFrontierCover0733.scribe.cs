using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0733Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0733.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0733",
        H("Original frontier context coverage 0733"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35187", "selected_cut_35187", "Selected cut at depth 12, code 284262, node 922593",
                "At remaining fuel 9 and original index 922593, selection on the full partial prefix of depth 12 and code 284262 returns the complete row with depth 12, base-four code 284262, original node 922593, kind 2, reserved field 0, 1613 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35234", "selected_cut_35234", "Selected cut at depth 11, code 71081, node 923681",
                "At remaining fuel 10 and original index 923681, selection on the full partial prefix of depth 11 and code 71081 returns the complete row with depth 11, base-four code 71081, original node 923681, kind 2, reserved field 0, 2393 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71065-922616", "unmarked_context_11_71065_922616", "Unmarked parent at depth 11, code 71065",
                "The frontier Boolean is false at remaining fuel 10, original node 922616, the whole prefixCache at depth 11 and code 71065, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-17769-923610", "unmarked_context_10_17769_923610", "Unmarked parent at depth 10, code 17769",
                "The frontier Boolean is false at remaining fuel 11, original node 923610, the whole prefixCache at depth 10 and code 17769, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71065-922616", "node_context_11_71065_922616", "Original split at fuel 10 and node 922616",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 922564, 896706, 922593, 922615. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-17769-923610", "node_context_10_17769_923610", "Original split at fuel 11 and node 923610",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 923494, 892405, 923542, 923609. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-284262-922593", "context_12_284262_922593", "Context at depth 12, code 284262, node 922593",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 284262 and original node 922593, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-71081-923681", "context_11_71081_923681", "Context at depth 11, code 71081, node 923681",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71081 and original node 923681, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
