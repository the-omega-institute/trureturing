using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0782Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0782.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0782",
        H("Original frontier context coverage 0782"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37539", "selected_cut_37539", "Selected cut at depth 11, code 74976, node 907917",
                "At remaining fuel 10 and original index 907917, selection on the full partial prefix of depth 11 and code 74976 returns the complete row with depth 11, base-four code 74976, original node 907917, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37586", "selected_cut_37586", "Selected cut at depth 13, code 1200185, node 1005744",
                "At remaining fuel 8 and original index 1005744, selection on the full partial prefix of depth 13 and code 1200185 returns the complete row with depth 13, base-four code 1200185, original node 1005744, kind 2, reserved field 0, 1401 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-9-4685-1004072", "unmarked_context_9_4685_1004072", "Unmarked parent at depth 9, code 4685",
                "The frontier Boolean is false at remaining fuel 12, original node 1004072, the whole prefixCache at depth 9 and code 4685, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-300044-1005607", "unmarked_context_12_300044_1005607", "Unmarked parent at depth 12, code 300044",
                "The frontier Boolean is false at remaining fuel 9, original node 1005607, the whole prefixCache at depth 12 and code 300044, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-9-4685-1004072", "node_context_9_4685_1004072", "Original split at fuel 12 and node 1004072",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1003182, 893098, 1003653, 1004071. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-300044-1005607", "node_context_12_300044_1005607", "Original split at fuel 9 and node 1005607",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1005547, 1005572, 1005598, 1005606. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-9-4685-1004072", "context_9_4685_1004072", "Context at depth 9, code 4685, node 1004072",
                "The conclusion is adaptive Accepted at the exact depth 9, full base-four code 4685 and original node 1004072, hence remaining fuel 12, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_10_18740_1003182, context_10_18741_893098, context_10_18742_1003653, context_10_18743_1004071.", DescribeRole.Theorem),
            Node("context-13-1200185-1005744", "context_13_1200185_1005744", "Context at depth 13, code 1200185, node 1005744",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1200185 and original node 1005744, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
