using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part008;

internal sealed class PreparedEJMCompleteFrontierCover0769Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part008/PreparedEJMCompleteFrontierCover0769.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0769",
        H("Original frontier context coverage 0769"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36913", "selected_cut_36913", "Selected cut at depth 11, code 74752, node 167448",
                "At remaining fuel 10 and original index 167448, selection on the full partial prefix of depth 11 and code 74752 returns the complete row with depth 11, base-four code 74752, original node 167448, kind 1, reserved field 0, 1 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36961", "selected_cut_36961", "Selected cut at depth 12, code 299059, node 986665",
                "At remaining fuel 9 and original index 986665, selection on the full partial prefix of depth 12 and code 299059 returns the complete row with depth 12, base-four code 299059, original node 986665, kind 2, reserved field 0, 2117 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-74753-984966", "unmarked_context_11_74753_984966", "Unmarked parent at depth 11, code 74753",
                "The frontier Boolean is false at remaining fuel 10, original node 984966, the whole prefixCache at depth 11 and code 74753, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-74764-986666", "unmarked_context_11_74764_986666", "Unmarked parent at depth 11, code 74764",
                "The frontier Boolean is false at remaining fuel 10, original node 986666, the whole prefixCache at depth 11 and code 74764, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-74753-984966", "node_context_11_74753_984966", "Original split at fuel 10 and node 984966",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 984786, 984848, 984906, 984965. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-74764-986666", "node_context_11_74764_986666", "Original split at fuel 10 and node 986666",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 985390, 986601, 986630, 986665. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-11-74752-167448", "context_11_74752_167448", "Context at depth 11, code 74752, node 167448",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 74752 and original node 167448, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-74764-986666", "context_11_74764_986666", "Context at depth 11, code 74764, node 986666",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 74764 and original node 986666, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its unmarked equation, literal split equation and all four child conclusions: context_12_299056_985390, context_12_299057_986601, context_12_299058_986630, context_12_299059_986665.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
