using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part010;

internal sealed class PreparedEJMCompleteFrontierCover0988Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part010/PreparedEJMCompleteFrontierCover0988.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0988",
        H("Original frontier context coverage 0988"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-47427", "selected_cut_47427", "Selected cut at depth 12, code 373296, node 1255011",
                "At remaining fuel 9 and original index 1255011, selection on the full partial prefix of depth 12 and code 373296 returns the complete row with depth 12, base-four code 373296, original node 1255011, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-47475", "selected_cut_47475", "Selected cut at depth 11, code 93351, node 1328819",
                "At remaining fuel 10 and original index 1328819, selection on the full partial prefix of depth 11 and code 93351 returns the complete row with depth 11, base-four code 93351, original node 1328819, kind 2, reserved field 0, 1877 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-93324-1327341", "unmarked_context_11_93324_1327341", "Unmarked parent at depth 11, code 93324",
                "The frontier Boolean is false at remaining fuel 10, original node 1327341, the whole prefixCache at depth 11 and code 93324, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-23336-1328661", "unmarked_context_10_23336_1328661", "Unmarked parent at depth 10, code 23336",
                "The frontier Boolean is false at remaining fuel 11, original node 1328661, the whole prefixCache at depth 10 and code 23336, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-93324-1327341", "node_context_11_93324_1327341", "Original split at fuel 10 and node 1327341",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1255011, 1327272, 1327300, 1327340. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-23336-1328661", "node_context_10_23336_1328661", "Original split at fuel 11 and node 1328661",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 907917, 1328558, 1328618, 1328660. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-373296-1255011", "context_12_373296_1255011", "Context at depth 12, code 373296, node 1255011",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 373296 and original node 1255011, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-93351-1328819", "context_11_93351_1328819", "Context at depth 11, code 93351, node 1328819",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 93351 and original node 1328819, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
