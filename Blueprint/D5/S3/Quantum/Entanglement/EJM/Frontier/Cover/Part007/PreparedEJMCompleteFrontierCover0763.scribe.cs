using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part007;

internal sealed class PreparedEJMCompleteFrontierCover0763Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part007/PreparedEJMCompleteFrontierCover0763.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0763",
        H("Original frontier context coverage 0763"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-36627", "selected_cut_36627", "Selected cut at depth 12, code 289605, node 896706",
                "At remaining fuel 9 and original index 896706, selection on the full partial prefix of depth 12 and code 289605 returns the complete row with depth 12, base-four code 289605, original node 896706, kind 1, reserved field 0, 1 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-36675", "selected_cut_36675", "Selected cut at depth 12, code 289677, node 973815",
                "At remaining fuel 9 and original index 973815, selection on the full partial prefix of depth 12 and code 289677 returns the complete row with depth 12, base-four code 289677, original node 973815, kind 2, reserved field 0, 1549 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-72401-972698", "unmarked_context_11_72401_972698", "Unmarked parent at depth 11, code 72401",
                "The frontier Boolean is false at remaining fuel 10, original node 972698, the whole prefixCache at depth 11 and code 72401, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-72418-973757", "unmarked_context_11_72418_973757", "Unmarked parent at depth 11, code 72418",
                "The frontier Boolean is false at remaining fuel 10, original node 973757, the whole prefixCache at depth 11 and code 72418, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-72401-972698", "node_context_11_72401_972698", "Original split at fuel 10 and node 972698",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 972624, 896706, 972659, 972697. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-72418-973757", "node_context_11_72418_973757", "Original split at fuel 10 and node 973757",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 973686, 973712, 973733, 973756. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-289605-896706", "context_12_289605_896706", "Context at depth 12, code 289605, node 896706",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289605 and original node 896706, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-12-289677-973815", "context_12_289677_973815", "Context at depth 12, code 289677, node 973815",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 289677 and original node 973815, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
