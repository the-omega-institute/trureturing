using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0353Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0353.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0353",
        H("Original frontier context coverage 0353"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-16947", "selected_cut_16947", "Selected cut at depth 12, code 28497, node 170504",
                "At remaining fuel 9 and original index 170504, selection on the full partial prefix of depth 12 and code 28497 returns the complete row with depth 12, base-four code 28497, original node 170504, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-16995", "selected_cut_16995", "Selected cut at depth 13, code 114084, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 114084 returns the complete row with depth 13, base-four code 114084, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-28498-430840", "unmarked_context_12_28498_430840", "Unmarked parent at depth 12, code 28498",
                "The frontier Boolean is false at remaining fuel 9, original node 430840, the whole prefixCache at depth 12 and code 28498, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-7129-431855", "unmarked_context_11_7129_431855", "Unmarked parent at depth 11, code 7129",
                "The frontier Boolean is false at remaining fuel 10, original node 431855, the whole prefixCache at depth 11 and code 7129, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-28498-430840", "node_context_12_28498_430840", "Original split at fuel 9 and node 430840",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 430805, 430831, 430839. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-7129-431855", "node_context_11_7129_431855", "Original split at fuel 10 and node 431855",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 431768, 431769, 431812, 431854. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-28497-170504", "context_12_28497_170504", "Context at depth 12, code 28497, node 170504",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 28497 and original node 170504, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-114084-3444", "context_13_114084_3444", "Context at depth 13, code 114084, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 114084 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
