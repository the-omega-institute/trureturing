using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part005;

internal sealed class PreparedEJMCompleteFrontierCover0573Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part005/PreparedEJMCompleteFrontierCover0573.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0573",
        H("Original frontier context coverage 0573"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 49 exact cut-selection equations, and 15 literal split equations paired with 15 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-27507", "selected_cut_27507", "Selected cut at depth 13, code 366684, node 695499",
                "At remaining fuel 8 and original index 695499, selection on the full partial prefix of depth 13 and code 366684 returns the complete row with depth 13, base-four code 366684, original node 695499, kind 2, reserved field 0, 3057 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-27555", "selected_cut_27555", "Selected cut at depth 13, code 366735, node 696448",
                "At remaining fuel 8 and original index 696448, selection on the full partial prefix of depth 13 and code 366735 returns the complete row with depth 13, base-four code 366735, original node 696448, kind 2, reserved field 0, 717 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-91671-695595", "unmarked_context_12_91671_695595", "Unmarked parent at depth 12, code 91671",
                "The frontier Boolean is false at remaining fuel 9, original node 695595, the whole prefixCache at depth 12 and code 91671, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-12-91681-696328", "unmarked_context_12_91681_696328", "Unmarked parent at depth 12, code 91681",
                "The frontier Boolean is false at remaining fuel 9, original node 696328, the whole prefixCache at depth 12 and code 91681, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-91671-695595", "node_context_12_91671_695595", "Original split at fuel 9 and node 695595",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 695499, 695555, 695582, 695594. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-12-91681-696328", "node_context_12_91681_696328", "Original split at fuel 9 and node 696328",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 696280, 696306, 696323, 696327. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-366684-695499", "context_13_366684_695499", "Context at depth 13, code 366684, node 695499",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 366684 and original node 695499, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-366735-696448", "context_13_366735_696448", "Context at depth 13, code 366735, node 696448",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 366735 and original node 696448, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
