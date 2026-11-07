using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0789Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0789.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0789",
        H("Original frontier context coverage 0789"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-37875", "selected_cut_37875", "Selected cut at depth 13, code 1202214, node 1015907",
                "At remaining fuel 8 and original index 1015907, selection on the full partial prefix of depth 13 and code 1202214 returns the complete row with depth 13, base-four code 1202214, original node 1015907, kind 2, reserved field 0, 1033 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-37922", "selected_cut_37922", "Selected cut at depth 12, code 300584, node 1017467",
                "At remaining fuel 9 and original index 1017467, selection on the full partial prefix of depth 12 and code 300584 returns the complete row with depth 12, base-four code 300584, original node 1017467, kind 2, reserved field 0, 3849 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-300553-1015918", "unmarked_context_12_300553_1015918", "Unmarked parent at depth 12, code 300553",
                "The frontier Boolean is false at remaining fuel 9, original node 1015918, the whole prefixCache at depth 12 and code 300553, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-75145-1017411", "unmarked_context_11_75145_1017411", "Unmarked parent at depth 11, code 75145",
                "The frontier Boolean is false at remaining fuel 10, original node 1017411, the whole prefixCache at depth 11 and code 75145, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-300553-1015918", "node_context_12_300553_1015918", "Original split at fuel 9 and node 1015918",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 1015858, 1015885, 1015907, 1015917. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-75145-1017411", "node_context_11_75145_1017411", "Original split at fuel 10 and node 1017411",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1017253, 1017310, 1017354, 1017410. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-1202214-1015907", "context_13_1202214_1015907", "Context at depth 13, code 1202214, node 1015907",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 1202214 and original node 1015907, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-300584-1017467", "context_12_300584_1017467", "Context at depth 12, code 300584, node 1017467",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 300584 and original node 1017467, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
