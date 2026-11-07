using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.EJM.Frontier.Cover.Part003;

internal sealed class PreparedEJMCompleteFrontierCover0301Document : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/EJM/Frontier/Cover/Part003/PreparedEJMCompleteFrontierCover0301.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original frontier context coverage 0301",
        H("Original frontier context coverage 0301"),
        Blocks(
            Paragraph(Text("The original replay uses twenty coordinates with four values each. A suffix retains remaining fuel, its original finite node index, the whole prefix cache and the whole partial assignment. Depth distinguishes leading zero values in a base-four prefix.")),
            Paragraph(Text("At a split, all four values 0, 1, 2 and 3 are required, with the corresponding original child indices, cache updates and partial-assignment updates.")),
            Paragraph(Text("This module has 64 context conclusions, 48 exact cut-selection equations, and 16 literal split equations paired with 16 unmarked-context equations. These are inputs to the full original frontier root through the context assembly chain.")),
            Node("selected-cut-14452", "selected_cut_14452", "Selected cut at depth 13, code 108847, node 373073",
                "At remaining fuel 8 and original index 373073, selection on the full partial prefix of depth 13 and code 108847 returns the complete row with depth 13, base-four code 108847, original node 373073, kind 2, reserved field 0, 925 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("selected-cut-14499", "selected_cut_14499", "Selected cut at depth 13, code 108918, node 373939",
                "At remaining fuel 8 and original index 373939, selection on the full partial prefix of depth 13 and code 108918 returns the complete row with depth 13, base-four code 108918, original node 373939, kind 2, reserved field 0, 1865 subtree occurrences and completion domain 16384. The proof reduces this concrete selection equation.", DescribeRole.Theorem),
            Node("unmarked-context-12-27211-373074", "unmarked_context_12_27211_373074", "Unmarked parent at depth 12, code 27211",
                "The frontier Boolean is false at remaining fuel 9, original node 373074, the whole prefixCache at depth 12 and code 27211, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("unmarked-context-11-6806-373847", "unmarked_context_11_6806_373847", "Unmarked parent at depth 11, code 6806",
                "The frontier Boolean is false at remaining fuel 10, original node 373847, the whole prefixCache at depth 11 and code 6806, and the matching prefixPartial. This is the unmarked premise used by the parent split assembly.", DescribeRole.Theorem),
            Node("node-context-12-27211-373074", "node_context_12_27211_373074", "Original split at fuel 9 and node 373074",
                "The complete original decoder output is the split at coordinate 12, with value children 0 through 3 respectively at original indices 3444, 373046, 373064, 373073. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("node-context-11-6806-373847", "node_context_11_6806_373847", "Original split at fuel 10 and node 373847",
                "The complete original decoder output is the split at coordinate 11, with value children 0 through 3 respectively at original indices 373701, 373737, 373801, 373846. The proof applies checked_split_node to the finite literal check; every child edge is retained.", DescribeRole.Theorem),
            Node("context-13-108847-373073", "context_13_108847_373073", "Context at depth 13, code 108847, node 373073",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108847 and original node 373073, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem),
            Node("context-13-108918-373939", "context_13_108918_373939", "Context at depth 13, code 108918, node 373939",
                "The conclusion is adaptive Accepted at the exact depth 13, full base-four code 108918 and original node 373939, hence remaining fuel 8, with the whole canonical prefix cache and partial assignment. The proof uses its exact selected-cut equation and accepted_of_selected at this same prefix.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string declaration, string title, string prose,
        DescribeRole role) => Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
