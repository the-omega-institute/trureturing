using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0277Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0277.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0277",
        H("Original frontier context coverage 0277"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-13299", "selected_cut_13299", "Selected cut at depth 13, code 106620, node 350418",
                "At remaining fuel 8 and original index 350418, selection on the full partial prefix of depth 13 and code 106620 returns the complete row with depth 13, base-four code 106620, original node 350418, kind 2, reserved field 0, 1201 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-13346", "selected_cut_13346", "Selected cut at depth 13, code 106676, node 351298",
                "At remaining fuel 8 and original index 351298, selection on the full partial prefix of depth 13 and code 106676 returns the complete row with depth 13, base-four code 106676, original node 351298, kind 2, reserved field 0, 641 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-26655-350475", "unmarked_context_12_26655_350475", "Unmarked parent at depth 12, code 26655",
                "The frontier Boolean is false at remaining fuel 9, original node 350475, the whole prefixCache at depth 12 and code 26655, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-26668-351287", "unmarked_context_12_26668_351287", "Unmarked parent at depth 12, code 26668",
                "The frontier Boolean is false at remaining fuel 9, original node 351287, the whole prefixCache at depth 12 and code 26668, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-26655-350475", "node_context_12_26655_350475", "Original split at fuel 9 and node 350475",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 350418, 350451, 350470, 350474. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-26668-351287", "node_context_12_26668_351287", "Original split at fuel 9 and node 351287",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 351244, 351267, 351282, 351286. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-106620-350418", "context_13_106620_350418", "Context at depth 13, code 106620, node 350418",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106620 and original node 350418, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-106676-351298", "context_13_106676_351298", "Context at depth 13, code 106676, node 351298",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 106676 and original node 351298, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
