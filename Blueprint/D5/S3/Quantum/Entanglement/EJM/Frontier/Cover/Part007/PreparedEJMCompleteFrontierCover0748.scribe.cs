using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0748Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0748.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0748",
        H("Original frontier context coverage 0748"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-35907", "selected_cut_35907", "Selected cut at depth 12, code 287517, node 946101",
                "At remaining fuel 9 and original index 946101, selection on the full partial prefix of depth 12 and code 287517 returns the complete row with depth 12, base-four code 287517, original node 946101, kind 2, reserved field 0, 3357 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-35954", "selected_cut_35954", "Selected cut at depth 12, code 287567, node 903806",
                "At remaining fuel 9 and original index 903806, selection on the full partial prefix of depth 12 and code 287567 returns the complete row with depth 12, base-four code 287567, original node 903806, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-71879-946150", "unmarked_context_11_71879_946150", "Unmarked parent at depth 11, code 71879",
                "The frontier Boolean is false at remaining fuel 10, original node 946150, the whole prefixCache at depth 11 and code 71879, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-71891-948021", "unmarked_context_11_71891_948021", "Unmarked parent at depth 11, code 71891",
                "The frontier Boolean is false at remaining fuel 10, original node 948021, the whole prefixCache at depth 11 and code 71891, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-71879-946150", "node_context_11_71879_946150", "Original split at fuel 10 and node 946150",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 946046, 946101, 946149, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-71891-948021", "node_context_11_71891_948021", "Original split at fuel 10 and node 948021",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 947983, 896706, 948020, 903806. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-287517-946101", "context_12_287517_946101", "Context at depth 12, code 287517, node 946101",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 287517 and original node 946101, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-71891-948021", "context_11_71891_948021", "Context at depth 11, code 71891, node 948021",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 71891 and original node 948021, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_287564_947983, context_12_287565_896706, context_12_287566_948020, context_12_287567_903806.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
