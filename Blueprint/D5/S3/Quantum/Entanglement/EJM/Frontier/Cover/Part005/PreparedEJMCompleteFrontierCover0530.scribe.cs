using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0530Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0530.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0530",
        H("Original frontier context coverage 0530"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-25443", "selected_cut_25443", "Selected cut at depth 14, code 1400994, node 643807",
                "At remaining fuel 7 and original index 643807, selection on the full partial prefix of depth 14 and code 1400994 returns the complete row with depth 14, base-four code 1400994, original node 643807, kind 2, reserved field 0, 977 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-25490", "selected_cut_25490", "Selected cut at depth 13, code 350306, node 644995",
                "At remaining fuel 8 and original index 644995, selection on the full partial prefix of depth 13 and code 350306 returns the complete row with depth 13, base-four code 350306, original node 644995, kind 2, reserved field 0, 1413 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-13-350248-643845", "unmarked_context_13_350248_643845", "Unmarked parent at depth 13, code 350248",
                "The frontier Boolean is false at remaining fuel 8, original node 643845, the whole prefixCache at depth 13 and code 350248, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-21893-644935", "unmarked_context_11_21893_644935", "Unmarked parent at depth 11, code 21893",
                "The frontier Boolean is false at remaining fuel 10, original node 644935, the whole prefixCache at depth 11 and code 21893, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-13-350248-643845", "node_context_13_350248_643845", "Original split at fuel 8 and node 643845",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 643753, 643785, 643807, 643844. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-21893-644935", "node_context_11_21893_644935", "Original split at fuel 10 and node 644935",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 644701, 308705, 644817, 644934. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-14-1400994-643807", "context_14_1400994_643807", "Context at depth 14, code 1400994, node 643807",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 1400994 and original node 643807, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-350306-644995", "context_13_350306_644995", "Context at depth 13, code 350306, node 644995",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 350306 and original node 644995, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
