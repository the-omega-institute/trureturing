using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part009;

internal sealed class PreparedEJMCompleteFrontierCover0906Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part009/PreparedEJMCompleteFrontierCover0906.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0906",
        H("Original frontier context coverage 0906"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-43491", "selected_cut_43491", "Selected cut at depth 12, code 350757, node 1190897",
                "At remaining fuel 9 and original index 1190897, selection on the full partial prefix of depth 12 and code 350757 returns the complete row with depth 12, base-four code 350757, original node 1190897, kind 2, reserved field 0, 2365 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-43539", "selected_cut_43539", "Selected cut at depth 11, code 87711, node 1192614",
                "At remaining fuel 10 and original index 1192614, selection on the full partial prefix of depth 11 and code 87711 returns the complete row with depth 11, base-four code 87711, original node 1192614, kind 2, reserved field 0, 2513 subtree occurrences and completion domain 262144. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-87689-1190970", "unmarked_context_11_87689_1190970", "Unmarked parent at depth 11, code 87689",
                "The frontier Boolean is false at remaining fuel 10, original node 1190970, the whole prefixCache at depth 11 and code 87689, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-21926-1192397", "unmarked_context_10_21926_1192397", "Unmarked parent at depth 10, code 21926",
                "The frontier Boolean is false at remaining fuel 11, original node 1192397, the whole prefixCache at depth 10 and code 21926, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-87689-1190970", "node_context_11_87689_1190970", "Original split at fuel 10 and node 1190970",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 1190851, 1190897, 1190929, 1190969. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-21926-1192397", "node_context_10_21926_1192397", "Original split at fuel 11 and node 1192397",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 1192250, 1192304, 900587, 1192396. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-350757-1190897", "context_12_350757_1190897", "Context at depth 12, code 350757, node 1190897",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 350757 and original node 1190897, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-11-87711-1192614", "context_11_87711_1192614", "Context at depth 11, code 87711, node 1192614",
                "The conclusion is adaptive Accepted at the exact depth 11, full base-four code 87711 and original node 1192614, hence remaining fuel 10, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
