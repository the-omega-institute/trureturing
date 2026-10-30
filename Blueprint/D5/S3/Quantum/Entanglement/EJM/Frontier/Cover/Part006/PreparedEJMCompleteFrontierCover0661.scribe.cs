using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part006;

internal sealed class PreparedEJMCompleteFrontierCover0661Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part006/PreparedEJMCompleteFrontierCover0661.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0661",
        H("Original frontier context coverage 0661"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 47 exact cut-selection equations, and 17 literal split equations paired with 17 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-31732", "selected_cut_31732", "Selected cut at depth 12, code 106147, node 814129",
                "At remaining fuel 9 and original index 814129, selection on the full partial prefix of depth 12 and code 106147 returns the complete row with depth 12, base-four code 106147, original node 814129, kind 2, reserved field 0, 1693 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-31778", "selected_cut_31778", "Selected cut at depth 13, code 430151, node 815428",
                "At remaining fuel 8 and original index 815428, selection on the full partial prefix of depth 13 and code 430151 returns the complete row with depth 13, base-four code 430151, original node 815428, kind 2, reserved field 0, 757 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-26536-814130", "unmarked_context_11_26536_814130", "Unmarked parent at depth 11, code 26536",
                "The frontier Boolean is false at remaining fuel 10, original node 814130, the whole prefixCache at depth 11 and code 26536, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-10-6720-815336", "unmarked_context_10_6720_815336", "Unmarked parent at depth 10, code 6720",
                "The frontier Boolean is false at remaining fuel 11, original node 815336, the whole prefixCache at depth 10 and code 6720, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-26536-814130", "node_context_11_26536_814130", "Original split at fuel 10 and node 814130",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 814094, 814108, 769937, 814129. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-10-6720-815336", "node_context_10_6720_815336", "Original split at fuel 11 and node 815336",
                "The complete original decoder output is the split at coordinate 10, with value children 0 through 3 respectively at original indices 434745, 167448, 815333, 815335. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-106147-814129", "context_12_106147_814129", "Context at depth 12, code 106147, node 814129",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 106147 and original node 814129, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-430151-815428", "context_13_430151_815428", "Context at depth 13, code 430151, node 815428",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 430151 and original node 815428, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
