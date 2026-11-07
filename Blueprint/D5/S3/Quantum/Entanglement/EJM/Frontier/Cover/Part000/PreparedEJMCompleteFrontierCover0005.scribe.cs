using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part000;

internal sealed class PreparedEJMCompleteFrontierCover0005Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part000/PreparedEJMCompleteFrontierCover0005.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0005",
        H("Original frontier context coverage 0005"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-00242", "selected_cut_00242", "Selected cut at depth 12, code 362, node 13269",
                "At remaining fuel 9 and original index 13269, selection on the full partial prefix of depth 12 and code 362 returns the complete row with depth 12, base-four code 362, original node 13269, kind 2, reserved field 0, 2785 subtree occurrences and completion domain 65536. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-00289", "selected_cut_00289", "Selected cut at depth 13, code 5146, node 15633",
                "At remaining fuel 8 and original index 15633, selection on the full partial prefix of depth 13 and code 5146 returns the complete row with depth 13, base-four code 5146, original node 15633, kind 2, reserved field 0, 2805 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-11-90-13348", "unmarked_context_11_90_13348", "Unmarked parent at depth 11, code 90",
                "The frontier Boolean is false at remaining fuel 10, original node 13348, the whole prefixCache at depth 11 and code 90, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-13-5144-15518", "unmarked_context_13_5144_15518", "Unmarked parent at depth 13, code 5144",
                "The frontier Boolean is false at remaining fuel 8, original node 15518, the whole prefixCache at depth 13 and code 5144, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-11-90-13348", "node_context_11_90_13348", "Original split at fuel 10 and node 13348",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 13140, 13202, 13269, 13347. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-13-5144-15518", "node_context_13_5144_15518", "Original split at fuel 8 and node 15518",
                "The complete original decoder output is the split at coordinate 13, with value children 0 through 3 respectively at original indices 15418, 15454, 15489, 15517. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-12-362-13269", "context_12_362_13269", "Context at depth 12, code 362, node 13269",
                "The conclusion is adaptive Accepted at the exact depth 12, full base-four code 362 and original node 13269, hence remaining fuel 9, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-5146-15633", "context_13_5146_15633", "Context at depth 13, code 5146, node 15633",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 5146 and original node 15633, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
