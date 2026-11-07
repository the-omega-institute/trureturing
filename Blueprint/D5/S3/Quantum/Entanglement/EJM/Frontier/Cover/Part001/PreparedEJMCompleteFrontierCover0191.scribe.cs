using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part001;

internal sealed class PreparedEJMCompleteFrontierCover0191Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part001/PreparedEJMCompleteFrontierCover0191.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0191",
        H("Original frontier context coverage 0191"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09171", "selected_cut_09171", "Selected cut at depth 13, code 93288, node 254162",
                "At remaining fuel 8 and original index 254162, selection on the full partial prefix of depth 13 and code 93288 returns the complete row with depth 13, base-four code 93288, original node 254162, kind 2, reserved field 0, 1913 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09218", "selected_cut_09218", "Selected cut at depth 13, code 93332, node 255254",
                "At remaining fuel 8 and original index 255254, selection on the full partial prefix of depth 13 and code 93332 returns the complete row with depth 13, base-four code 93332, original node 255254, kind 2, reserved field 0, 1025 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-23322-254246", "unmarked_context_12_23322_254246", "Unmarked parent at depth 12, code 23322",
                "The frontier Boolean is false at remaining fuel 9, original node 254246, the whole prefixCache at depth 12 and code 23322, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-23332-255239", "unmarked_context_12_23332_255239", "Unmarked parent at depth 12, code 23332",
                "The frontier Boolean is false at remaining fuel 9, original node 255239, the whole prefixCache at depth 12 and code 23332, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-23322-254246", "node_context_12_23322_254246", "Original split at fuel 9 and node 254246",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 254162, 254205, 254237, 254245. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-23332-255239", "node_context_12_23332_255239", "Original split at fuel 9 and node 255239",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 255161, 255213, 255232, 255238. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-93288-254162", "context_13_93288_254162", "Context at depth 13, code 93288, node 254162",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93288 and original node 254162, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-93332-255254", "context_13_93332_255254", "Context at depth 13, code 93332, node 255254",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 93332 and original node 255254, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
