using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part002;

internal sealed class PreparedEJMCompleteFrontierCover0202Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part002/PreparedEJMCompleteFrontierCover0202.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0202",
        H("Original frontier context coverage 0202"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-09699", "selected_cut_09699", "Selected cut at depth 12, code 24624, node 267906",
                "At remaining fuel 9 and original index 267906, selection on the full partial prefix of depth 12 and code 24624 returns the complete row with depth 12, base-four code 24624, original node 267906, kind 2, reserved field 0, 3297 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-09745", "selected_cut_09745", "Selected cut at depth 13, code 98596, node 3444",
                "At remaining fuel 8 and original index 3444, selection on the full partial prefix of depth 13 and code 98596 returns the complete row with depth 13, base-four code 98596, original node 3444, kind 1, reserved field 0, 1 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6155-267818", "unmarked_context_11_6155_267818", "Unmarked parent at depth 11, code 6155",
                "The frontier Boolean is false at remaining fuel 10, original node 267818, the whole prefixCache at depth 11 and code 6155, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6161-269025", "unmarked_context_11_6161_269025", "Unmarked parent at depth 11, code 6161",
                "The frontier Boolean is false at remaining fuel 10, original node 269025, the whole prefixCache at depth 11 and code 6161, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6155-267818", "node_context_11_6155_267818", "Original split at fuel 10 and node 267818",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 267665, 267719, 267772, 267817. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6161-269025", "node_context_11_6161_269025", "Original split at fuel 10 and node 269025",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 268916, 268917, 268968, 269024. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-6155-267818", "context_11_6155_267818", "Context at depth 11, code 6155, node 267818",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 6155 and original node 267818, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_24620_267665, context_12_24621_267719, context_12_24622_267772, context_12_24623_267817.", DescribeRole.Theorem),
            Node("context-13-98596-3444", "context_13_98596_3444", "Context at depth 13, code 98596, node 3444",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 98596 and original node 3444, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
