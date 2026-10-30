using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0124Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0124.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0124",
        H("Original frontier context coverage 0124"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-05954", "selected_cut_05954", "Selected cut at depth 13, code 84104, node 181697",
                "At remaining fuel 8 and original index 181697, selection on the full partial prefix of depth 13 and code 84104 returns the complete row with depth 13, base-four code 84104, original node 181697, kind 2, reserved field 0, 989 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-06002", "selected_cut_06002", "Selected cut at depth 13, code 84152, node 182640",
                "At remaining fuel 8 and original index 182640, selection on the full partial prefix of depth 13 and code 84152 returns the complete row with depth 13, base-four code 84152, original node 182640, kind 2, reserved field 0, 721 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-21026-181753", "unmarked_context_12_21026_181753", "Unmarked parent at depth 12, code 21026",
                "The frontier Boolean is false at remaining fuel 9, original node 181753, the whole prefixCache at depth 12 and code 21026, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-21037-182628", "unmarked_context_12_21037_182628", "Unmarked parent at depth 12, code 21037",
                "The frontier Boolean is false at remaining fuel 9, original node 182628, the whole prefixCache at depth 12 and code 21037, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-21026-181753", "node_context_12_21026_181753", "Original split at fuel 9 and node 181753",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 181697, 181728, 181745, 181752. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-21037-182628", "node_context_12_21037_182628", "Original split at fuel 9 and node 182628",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 182565, 182592, 182616, 182627. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-84104-181697", "context_13_84104_181697", "Context at depth 13, code 84104, node 181697",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84104 and original node 181697, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-84152-182640", "context_13_84152_182640", "Context at depth 13, code 84152, node 182640",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 84152 and original node 182640, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
