using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0294Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0294.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0294",
        H("Original frontier context coverage 0294"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14116", "selected_cut_14116", "Selected cut at depth 12, code 27055, node 366357",
                "At remaining fuel 9 and original index 366357, selection on the full partial prefix of depth 12 and code 27055 returns the complete row with depth 12, base-four code 27055, original node 366357, kind 2, reserved field 0, 1449 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14162", "selected_cut_14162", "Selected cut at depth 14, code 434258, node 367136",
                "At remaining fuel 7 and original index 367136, selection on the full partial prefix of depth 14 and code 434258 returns the complete row with depth 14, base-four code 434258, original node 367136, kind 2, reserved field 0, 837 subtree occurrences and completion domain 4096. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-6763-366358", "unmarked_context_11_6763_366358", "Unmarked parent at depth 11, code 6763",
                "The frontier Boolean is false at remaining fuel 10, original node 366358, the whole prefixCache at depth 11 and code 6763, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6784-367091", "unmarked_context_11_6784_367091", "Unmarked parent at depth 11, code 6784",
                "The frontier Boolean is false at remaining fuel 10, original node 367091, the whole prefixCache at depth 11 and code 6784, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-6763-366358", "node_context_11_6763_366358", "Original split at fuel 10 and node 366358",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 366313, 366330, 366345, 366357. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6784-367091", "node_context_11_6784_367091", "Original split at fuel 10 and node 367091",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 34034, 48867, 347601, 367090. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-27055-366357", "context_12_27055_366357", "Context at depth 12, code 27055, node 366357",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 27055 and original node 366357, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-14-434258-367136", "context_14_434258_367136", "Context at depth 14, code 434258, node 367136",
                "The conclusion is adaptive Accepted at the exact depth 14, full base-four code 434258 and original node 367136, hence remaining fuel 7, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
