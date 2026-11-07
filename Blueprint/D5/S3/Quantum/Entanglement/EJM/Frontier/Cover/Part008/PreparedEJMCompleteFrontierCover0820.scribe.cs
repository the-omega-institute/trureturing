using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0820Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0820.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0820",
        H("Original frontier context coverage 0820"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-39363", "selected_cut_39363", "Selected cut at depth 12, code 302913, node 1068034",
                "At remaining fuel 9 and original index 1068034, selection on the full partial prefix of depth 12 and code 302913 returns the complete row with depth 12, base-four code 302913, original node 1068034, kind 2, reserved field 0, 2841 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-39411", "selected_cut_39411", "Selected cut at depth 12, code 302982, node 984676",
                "At remaining fuel 9 and original index 984676, selection on the full partial prefix of depth 12 and code 302982 returns the complete row with depth 12, base-four code 302982, original node 984676, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-75728-1068110", "unmarked_context_11_75728_1068110", "Unmarked parent at depth 11, code 75728",
                "The frontier Boolean is false at remaining fuel 10, original node 1068110, the whole prefixCache at depth 11 and code 75728, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-9-4733-1069330", "unmarked_context_9_4733_1069330", "Unmarked parent at depth 9, code 4733",
                "The frontier Boolean is false at remaining fuel 12, original node 1069330, the whole prefixCache at depth 9 and code 4733, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-75728-1068110", "node_context_11_75728_1068110", "Original split at fuel 10 and node 1068110",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1051681, 1068034, 1068072, 1068109. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-9-4733-1069330", "node_context_9_4733_1069330", "Original split at fuel 12 and node 1069330",
                "The complete original decoder output is the split at coordinate 9, with value children 0 through 3 respectively at original indices 1068632, 893098, 1069035, 1069329. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-302913-1068034", "context_12_302913_1068034", "Context at depth 12, code 302913, node 1068034",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302913 and original node 1068034, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-302982-984676", "context_12_302982_984676", "Context at depth 12, code 302982, node 984676",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 302982 and original node 984676, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
